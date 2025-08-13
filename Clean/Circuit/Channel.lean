import Clean.Circuit.Provable

structure Channel (F : Type) where
  {α : TypeMap}
  [inst : ProvableType α]
  predicate : α F → Prop -- proven at yield site, available at use site

abbrev ChannelRegistry (F : Type) := Std.HashMap String (Channel F)

structure ChannelEntry (F : Type) where
  channelName : String
  entry : List F
  multiplicity : Int -- positive for yield, negative for use

def ChannelEntry.valid {F : Type} (self : ChannelEntry F) (reg : ChannelRegistry F) :=
  match reg[self.channelName]? with
  | none => False
  | some channel =>
    if h : self.entry.length = channel.inst.size then
      channel.predicate (channel.inst.fromElements (h ▸ Vector.fromList self.entry))
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

/-
In spirit, the balancing condition is:

def balanced {F : Type} [DecidableEq F] (entries : List (ChannelEntry F)) :=
  ∀ (channelName : String) (entry : List F),
    (((entries.filter (fun e => e.channelName = channelName ∧ e.entry = entry)).map (·.multiplicity) |>.sum) = 0)

but, we define something stronger that is computable.
 -/

def balanced {F : Type} [DecidableEq F] (state : ChannelState F) :=
  state.registry.keys.all (fun name =>
    let subLists := (state.entries.filter (fun (e : ChannelEntry F) => e.channelName = name)).splitBy (·.entry = ·.entry)
    subLists.all (fun lst => (lst.map (fun e => e.multiplicity) |>.sum) = 0)
  )

def globalCheck {F : Type} [DecidableEq F] (state : ChannelState F) :=
  List.all state.entries (ChannelEntry.wellFormed · state.registry) ∧
  balanced state
