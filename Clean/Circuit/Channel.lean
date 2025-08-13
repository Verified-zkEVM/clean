import Clean.Circuit.Provable

structure Channel (F : Type) where
  {α : TypeMap}
  [inst : ProvableType α]
  predicate : α F → Prop -- proven at yield site, available at use site

abbrev ChannelRegistry (F : Type) := Std.HashMap String (Channel F)

structure ChannelEntry (F : Type) where
  channelName : String
  entry : List (Expression F)
  multiplicity : Int -- positive for yield, negative for use

def ChannelEntry.valid {F : Type} [Field F] (self : ChannelEntry F) (reg : ChannelRegistry F) (env : Environment F) :=
  match reg[self.channelName]? with
  | none => False
  | some channel =>
    if h : self.entry.length = channel.inst.size then
      channel.predicate (channel.inst.fromElements (h ▸ eval (α:=ProvableVector field self.entry.length) env (Vector.fromList self.entry)))
    else
      False

def ChannelEntry.wellFormed {F : Type} (self : ChannelEntry F) (reg : ChannelRegistry F) :=
  match reg[self.channelName]? with
  | none => False
  | some channel => self.entry.length = channel.inst.size

instance {F : Type} (self : ChannelEntry F) (reg : ChannelRegistry F) :
    Decidable (self.wellFormed reg) := by
  unfold ChannelEntry.wellFormed
  match h : reg[self.channelName]? with
  | none => exact isFalse (by simp [h])
  | some channel => infer_instance

structure ChannelState (F : Type) where
  registry : ChannelRegistry F
  entries : List (ChannelEntry F)

def emptyChannelState {F : Type} : ChannelState F where
  registry := {}
  entries := []

def balanced {F : Type} [Field F] [DecidableEq F] (state : ChannelState F) (env : Environment F) :=
  state.registry.keys.all (fun name =>
    let subLists := (state.entries.filter (fun (e : ChannelEntry F) => e.channelName = name)).splitBy
      (fun a b => a.entry.map (eval env ·) = b.entry.map (eval (α:=field) env ·))
    subLists.all (fun lst => (lst.map (fun e => e.multiplicity) |>.sum) = 0)
  )

def globalCheck {F : Type} [Field F] [DecidableEq F] (state : ChannelState F) (env : Environment F) :=
  List.all state.entries (ChannelEntry.wellFormed · state.registry) ∧
  balanced state env
