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

def ChanelEntry.isValid {F : Type} (self : ChannelEntry F) (reg : ChannelRegistry F) :=
  match reg[self.channelName]? with
  | none => False
  | some channel =>
    if h : self.entry.length = channel.inst.size then
      channel.predicate (channel.inst.fromElements (h ▸ Vector.fromList self.entry))
    else
      False
