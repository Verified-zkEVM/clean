module

public import CompStark.Stark.ProgGen
public import CompStark.KoalaBear.Group
public import KeccakShowcase.Air
meta import KeccakShowcase.Air

/-! Part 3 of four of the chunks of the keccak-air showcase's quotient kernel
(`KeccakShowcase.Kernel`). -/

@[expose] public section

#gen_group_chunks KeccakShowcase.QuotientKernel CompStark.KoalaBear.Group
  (CompStark.Stark.Prog.compile (KeccakShowcase.air 6).constraints) 2000 2 4
