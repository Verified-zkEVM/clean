import Lean
import Lean.Elab.Frontend
import Lean.Elab.Import
import Mathlib.Util.CountHeartbeats

open Lean System Elab Command

structure CommandHeartbeat where
  name : String
  heartbeats : Nat

structure Args where
  file : String := ""
  setup? : Option FilePath := none
  jsonOutput : Bool := false
  opts : Options := {}

def parseD (opts : Options) (arg : String) : IO Options := do
  let pos := arg.find '='
  if h : pos.IsAtEnd then
    throw <| IO.userError s!"invalid -D argument {arg}"
  else
    let name := arg.sliceTo pos |>.toName
    let val := arg.sliceFrom (pos.next h) |>.copy
    if let some decl := (← getOptionDecls).find? name then
      Language.Lean.setOption opts decl name val
    else
      return opts.set name val

partial def parseArgs (args : List String) (acc : Args := {}) : IO Args := do
  match args with
  | [] => return acc
  | "--json" :: xs => parseArgs xs { acc with jsonOutput := true }
  | "--setup" :: x :: xs => parseArgs xs { acc with setup? := some x }
  | "-D" :: x :: xs => parseArgs xs { acc with opts := (← parseD acc.opts x) }
  | x :: xs =>
      if x.startsWith "-D" then
        parseArgs xs { acc with opts := (← parseD acc.opts (x.drop 2).toString) }
      else if x == "-o" || x == "--o" || x == "-i" || x == "--i" || x == "-c" || x == "--c" then
        match xs with
        | _ :: ys => parseArgs ys acc
        | [] => parseArgs [] acc
      else if acc.file == "" then
        parseArgs xs { acc with file := x }
      else
        parseArgs xs acc

def commandName (stx : Syntax) : String :=
  match stx.find? (·.isOfKind ``Parser.Command.declId) with
  | some decl => toString decl[0].getId
  | none => toString stx.getKind

def runCommandElabM
    (inputCtx : Parser.InputContext)
    (cmdPos : String.Pos.Raw)
    (x : CommandElabM α)
    (state : State) : IO (α × State) := do
  let cmdCtx : Context := {
    cmdPos
    fileName := inputCtx.fileName
    fileMap := inputCtx.fileMap
    snap? := none
    cancelTk? := none
  }
  match ← EIO.toIO' ((x cmdCtx).run state) with
  | Except.error e => throw <| IO.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok result => return result

partial def processCommandsWithHeartbeats
    (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState)
    (commandState : State)
    (acc : Array CommandHeartbeat := #[]) : IO (State × Array CommandHeartbeat) := do
  let scope := commandState.scopes.head!
  let pmctx := {
    env := commandState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls
  }
  let (cmd, parserState, messages) :=
    Parser.parseCommand inputCtx pmctx parserState commandState.messages
  let commandState := { commandState with messages }

  if Parser.isTerminalCommand cmd then
    return (commandState, acc)

  let (heartbeats, commandState) ←
    runCommandElabM inputCtx parserState.pos
      (Mathlib.CountHeartbeats.elabForHeartbeats ⟨cmd⟩)
      commandState

  let (_, commandState) ←
    runCommandElabM inputCtx parserState.pos (elabCommandTopLevel cmd) commandState

  processCommandsWithHeartbeats inputCtx parserState commandState
    (acc.push { name := commandName cmd, heartbeats := heartbeats / 1000 })

def runFrontendWithCommandHeartbeats
    (input : String)
    (opts : Options)
    (fileName : String)
    (mainModuleName : Name)
    (setup? : Option ModuleSetup := none) :
    IO (Option (Environment × Array CommandHeartbeat)) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  let opts := Elab.async.set opts false
  let (imports, isModule, mainModuleName, package?, importArts, plugins, opts) ←
    if let some setup := setup? then
      setup.dynlibs.forM Lean.loadDynlib
      pure (
        setup.imports?.getD (Elab.HeaderSyntax.imports header),
        strictOr setup.isModule (Elab.HeaderSyntax.isModule header),
        setup.name,
        setup.package?,
        setup.importArts,
        setup.plugins,
        opts.mergeBy (fun _ _ hOpt => hOpt) setup.options.toOptions
      )
    else
      pure (Elab.HeaderSyntax.imports header, Elab.HeaderSyntax.isModule header, mainModuleName, none, {}, #[], opts)
  let (env, messages) ← Elab.processHeaderCore (leakEnv := true)
    (Elab.HeaderSyntax.startPos header) imports isModule opts messages inputCtx 0 plugins mainModuleName package? importArts
  if messages.hasErrors then
    messages.forM fun msg => msg.toString >>= IO.eprintln
    return none
  let commandState := mkState env messages opts
  let (commandState, heartbeats) ← processCommandsWithHeartbeats inputCtx parserState commandState
  if commandState.messages.hasErrors then
    commandState.messages.forM fun msg => msg.toString >>= IO.eprintln
    return none
  return some (commandState.env, heartbeats)

def main (argv : List String) : IO UInt32 := do
  unsafe Lean.enableInitializersExecution
  let args ← parseArgs argv
  if args.file == "" then
    IO.eprintln "expected Lean file"
    return 1
  let contents ← IO.FS.readFile args.file
  let setup? ← args.setup?.mapM ModuleSetup.load
  let mainModuleName ←
    if let some setup := setup? then pure setup.name else moduleNameOfFileName args.file none
  let result? ← runFrontendWithCommandHeartbeats contents args.opts args.file mainModuleName setup?
  let some (_, commandHeartbeats) := result?
    | return 1
  let total := commandHeartbeats.foldl (· + ·.heartbeats) 0
  IO.println s!"HEARTBEATS {mainModuleName} {total}"
  for row in commandHeartbeats do
    if row.heartbeats > 0 then
      IO.println s!"COMMAND_HEARTBEATS {mainModuleName} {row.name} {row.heartbeats}"
  return 0
