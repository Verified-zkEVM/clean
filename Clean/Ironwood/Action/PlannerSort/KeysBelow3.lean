import Clean.Ironwood.Action.PlannerSort.Data

/-! Kernel-checked pdqsort recursion for Action region shapes with keys below three. -/

namespace Zcash.Circuits.Action.PlannerSort

open Halo2 FloorPlanner


def sortNode0Input : Array RegionShape :=
  #[⟨302, [], 0⟩, ⟨346, [], 0⟩]

def sortNode0Output : Array RegionShape :=
  #[⟨302, [], 0⟩, ⟨346, [], 0⟩]

def sortNode0Plan : Pdqsort.Plan :=
  .done

def sortNode0Layer : Pdqsort.Layer RegionShape :=
  .done sortNode0Output

set_option maxRecDepth 1000000 in
theorem sortNode0Layer_eq :
    Pdqsort.stepLayer sortNode0Input less (none)
      9 true true =
        sortNode0Layer := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sortNode0 :
    Pdqsort.recursePlanned 394 sortNode0Plan
      sortNode0Input less (none)
      9 true true =
        some sortNode0Output := by
  rw [Pdqsort.recursePlanned.eq_2,
    Pdqsort.recurseStepPlanned_eq_interpretLayer, sortNode0Layer_eq]
  simp only [Pdqsort.interpretLayer, sortNode0Layer]

def sortNode1Input : Array RegionShape :=
  #[⟨301, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨347, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨348, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨4, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨3, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨2, [.selector 5, .column .advice 0, .column .advice 1], 1⟩]

def sortNode1Output : Array RegionShape :=
  #[⟨301, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨347, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨348, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨4, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨3, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨2, [.selector 5, .column .advice 0, .column .advice 1], 1⟩]

def sortNode1Plan : Pdqsort.Plan :=
  .done

def sortNode1Layer : Pdqsort.Layer RegionShape :=
  .done sortNode1Output

set_option maxRecDepth 1000000 in
theorem sortNode1Layer_eq :
    Pdqsort.stepLayer sortNode1Input less (some ⟨244, [.column .advice 7], 1⟩)
      8 false false =
        sortNode1Layer := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sortNode1 :
    Pdqsort.recursePlanned 393 sortNode1Plan
      sortNode1Input less (some ⟨244, [.column .advice 7], 1⟩)
      8 false false =
        some sortNode1Output := by
  rw [Pdqsort.recursePlanned.eq_2,
    Pdqsort.recurseStepPlanned_eq_interpretLayer, sortNode1Layer_eq]
  simp only [Pdqsort.interpretLayer, sortNode1Layer]

def sortNode2Input : Array RegionShape :=
  #[⟨5, [.column .advice 0], 1⟩, ⟨6, [.column .advice 0], 1⟩, ⟨7, [.column .advice 0], 1⟩, ⟨364, [.column .advice 7], 1⟩, ⟨9, [.column .advice 6], 1⟩, ⟨362, [.column .advice 7], 1⟩, ⟨360, [.column .advice 7], 1⟩, ⟨12, [.column .advice 6], 1⟩, ⟨13, [.column .advice 6], 1⟩, ⟨359, [.column .advice 7], 1⟩, ⟨356, [.column .advice 7], 1⟩, ⟨354, [.column .advice 7], 1⟩, ⟨17, [.column .advice 6], 1⟩, ⟨353, [.column .advice 7], 1⟩, ⟨350, [.column .advice 7], 1⟩, ⟨20, [.column .advice 6], 1⟩, ⟨21, [.column .advice 6], 1⟩, ⟨349, [.column .advice 0], 1⟩, ⟨25, [.column .advice 6], 1⟩, ⟨2, [.selector 5, .column .advice 0, .column .advice 1], 1⟩, ⟨3, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨4, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨317, [.column .advice 6], 1⟩, ⟨28, [.column .advice 6], 1⟩, ⟨29, [.column .advice 6], 1⟩, ⟨315, [.column .advice 6], 1⟩, ⟨313, [.column .advice 6], 1⟩, ⟨312, [.column .advice 6], 1⟩, ⟨33, [.column .advice 6], 1⟩, ⟨309, [.column .advice 6], 1⟩, ⟨307, [.column .advice 6], 1⟩, ⟨36, [.column .advice 6], 1⟩, ⟨37, [.column .advice 6], 1⟩, ⟨306, [.column .advice 6], 1⟩, ⟨303, [.column .advice 6], 1⟩, ⟨133, [.column .advice 6], 1⟩, ⟨41, [.column .advice 6], 1⟩, ⟨348, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨347, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨301, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨298, [.column .advice 6], 1⟩, ⟨44, [.column .advice 6], 1⟩, ⟨45, [.column .advice 6], 1⟩, ⟨289, [.column .advice 6], 1⟩, ⟨287, [.column .advice 6], 1⟩, ⟨286, [.column .advice 6], 1⟩, ⟨49, [.column .advice 6], 1⟩, ⟨283, [.column .advice 6], 1⟩, ⟨265, [.column .advice 9], 1⟩, ⟨52, [.column .advice 6], 1⟩, ⟨53, [.column .advice 6], 1⟩, ⟨264, [.column .advice 9], 1⟩, ⟨261, [.column .advice 7], 1⟩, ⟨260, [.column .advice 7], 1⟩, ⟨57, [.column .advice 6], 1⟩, ⟨257, [.column .advice 7], 1⟩, ⟨253, [.column .advice 7], 1⟩, ⟨60, [.column .advice 6], 1⟩, ⟨61, [.column .advice 6], 1⟩, ⟨252, [.column .advice 7], 1⟩, ⟨249, [.column .advice 7], 1⟩, ⟨245, [.column .advice 7], 1⟩, ⟨65, [.column .advice 6], 1⟩, ⟨1, [.column .advice 0], 1⟩, ⟨241, [.column .advice 7], 1⟩, ⟨68, [.column .advice 6], 1⟩, ⟨69, [.column .advice 6], 1⟩, ⟨237, [.column .advice 7], 1⟩, ⟨236, [.column .advice 7], 1⟩, ⟨233, [.column .advice 7], 1⟩, ⟨73, [.column .advice 6], 1⟩, ⟨229, [.column .advice 7], 1⟩, ⟨228, [.column .advice 7], 1⟩, ⟨76, [.column .advice 6], 1⟩, ⟨77, [.column .advice 6], 1⟩, ⟨225, [.column .advice 7], 1⟩, ⟨221, [.column .advice 7], 1⟩, ⟨220, [.column .advice 7], 1⟩, ⟨81, [.column .advice 6], 1⟩, ⟨217, [.column .advice 7], 1⟩, ⟨213, [.column .advice 7], 1⟩, ⟨84, [.column .advice 6], 1⟩, ⟨85, [.column .advice 6], 1⟩, ⟨212, [.column .advice 7], 1⟩, ⟨209, [.column .advice 7], 1⟩, ⟨205, [.column .advice 7], 1⟩, ⟨89, [.column .advice 6], 1⟩, ⟨204, [.column .advice 7], 1⟩, ⟨201, [.column .advice 7], 1⟩, ⟨92, [.column .advice 6], 1⟩, ⟨93, [.column .advice 6], 1⟩, ⟨197, [.column .advice 7], 1⟩, ⟨196, [.column .advice 7], 1⟩, ⟨193, [.column .advice 7], 1⟩, ⟨97, [.column .advice 6], 1⟩, ⟨0, [.column .advice 0], 1⟩, ⟨189, [.column .advice 7], 1⟩, ⟨100, [.column .advice 6], 1⟩, ⟨101, [.column .advice 6], 1⟩, ⟨188, [.column .advice 7], 1⟩, ⟨185, [.column .advice 7], 1⟩, ⟨181, [.column .advice 7], 1⟩, ⟨105, [.column .advice 6], 1⟩, ⟨180, [.column .advice 7], 1⟩, ⟨177, [.column .advice 7], 1⟩, ⟨108, [.column .advice 6], 1⟩, ⟨109, [.column .advice 6], 1⟩, ⟨173, [.column .advice 7], 1⟩, ⟨172, [.column .advice 7], 1⟩, ⟨169, [.column .advice 7], 1⟩, ⟨113, [.column .advice 6], 1⟩, ⟨165, [.column .advice 7], 1⟩, ⟨164, [.column .advice 7], 1⟩, ⟨116, [.column .advice 6], 1⟩, ⟨117, [.column .advice 6], 1⟩, ⟨161, [.column .advice 7], 1⟩, ⟨157, [.column .advice 7], 1⟩, ⟨156, [.column .advice 7], 1⟩, ⟨121, [.column .advice 6], 1⟩, ⟨153, [.column .advice 7], 1⟩, ⟨149, [.column .advice 7], 1⟩, ⟨124, [.column .advice 6], 1⟩, ⟨125, [.column .advice 6], 1⟩, ⟨148, [.column .advice 7], 1⟩, ⟨145, [.column .advice 7], 1⟩, ⟨141, [.column .advice 7], 1⟩, ⟨129, [.column .advice 6], 1⟩, ⟨140, [.column .advice 7], 1⟩, ⟨137, [.column .advice 7], 1⟩, ⟨132, [.column .advice 6], 1⟩]

def sortNode2Output : Array RegionShape :=
  #[⟨25, [.column .advice 6], 1⟩, ⟨6, [.column .advice 0], 1⟩, ⟨7, [.column .advice 0], 1⟩, ⟨364, [.column .advice 7], 1⟩, ⟨9, [.column .advice 6], 1⟩, ⟨362, [.column .advice 7], 1⟩, ⟨360, [.column .advice 7], 1⟩, ⟨12, [.column .advice 6], 1⟩, ⟨13, [.column .advice 6], 1⟩, ⟨359, [.column .advice 7], 1⟩, ⟨356, [.column .advice 7], 1⟩, ⟨354, [.column .advice 7], 1⟩, ⟨17, [.column .advice 6], 1⟩, ⟨353, [.column .advice 7], 1⟩, ⟨350, [.column .advice 7], 1⟩, ⟨20, [.column .advice 6], 1⟩, ⟨21, [.column .advice 6], 1⟩, ⟨349, [.column .advice 0], 1⟩, ⟨241, [.column .advice 7], 1⟩, ⟨132, [.column .advice 6], 1⟩, ⟨137, [.column .advice 7], 1⟩, ⟨140, [.column .advice 7], 1⟩, ⟨317, [.column .advice 6], 1⟩, ⟨28, [.column .advice 6], 1⟩, ⟨1, [.column .advice 0], 1⟩, ⟨315, [.column .advice 6], 1⟩, ⟨313, [.column .advice 6], 1⟩, ⟨312, [.column .advice 6], 1⟩, ⟨33, [.column .advice 6], 1⟩, ⟨309, [.column .advice 6], 1⟩, ⟨307, [.column .advice 6], 1⟩, ⟨36, [.column .advice 6], 1⟩, ⟨37, [.column .advice 6], 1⟩, ⟨306, [.column .advice 6], 1⟩, ⟨303, [.column .advice 6], 1⟩, ⟨133, [.column .advice 6], 1⟩, ⟨41, [.column .advice 6], 1⟩, ⟨129, [.column .advice 6], 1⟩, ⟨141, [.column .advice 7], 1⟩, ⟨145, [.column .advice 7], 1⟩, ⟨298, [.column .advice 6], 1⟩, ⟨44, [.column .advice 6], 1⟩, ⟨45, [.column .advice 6], 1⟩, ⟨289, [.column .advice 6], 1⟩, ⟨287, [.column .advice 6], 1⟩, ⟨286, [.column .advice 6], 1⟩, ⟨49, [.column .advice 6], 1⟩, ⟨283, [.column .advice 6], 1⟩, ⟨265, [.column .advice 9], 1⟩, ⟨52, [.column .advice 6], 1⟩, ⟨53, [.column .advice 6], 1⟩, ⟨264, [.column .advice 9], 1⟩, ⟨261, [.column .advice 7], 1⟩, ⟨260, [.column .advice 7], 1⟩, ⟨57, [.column .advice 6], 1⟩, ⟨257, [.column .advice 7], 1⟩, ⟨253, [.column .advice 7], 1⟩, ⟨60, [.column .advice 6], 1⟩, ⟨61, [.column .advice 6], 1⟩, ⟨252, [.column .advice 7], 1⟩, ⟨249, [.column .advice 7], 1⟩, ⟨245, [.column .advice 7], 1⟩, ⟨65, [.column .advice 6], 1⟩, ⟨29, [.column .advice 6], 1⟩, ⟨68, [.column .advice 6], 1⟩, ⟨5, [.column .advice 0], 1⟩, ⟨69, [.column .advice 6], 1⟩, ⟨237, [.column .advice 7], 1⟩, ⟨236, [.column .advice 7], 1⟩, ⟨233, [.column .advice 7], 1⟩, ⟨73, [.column .advice 6], 1⟩, ⟨229, [.column .advice 7], 1⟩, ⟨228, [.column .advice 7], 1⟩, ⟨76, [.column .advice 6], 1⟩, ⟨77, [.column .advice 6], 1⟩, ⟨225, [.column .advice 7], 1⟩, ⟨221, [.column .advice 7], 1⟩, ⟨220, [.column .advice 7], 1⟩, ⟨81, [.column .advice 6], 1⟩, ⟨217, [.column .advice 7], 1⟩, ⟨213, [.column .advice 7], 1⟩, ⟨84, [.column .advice 6], 1⟩, ⟨85, [.column .advice 6], 1⟩, ⟨212, [.column .advice 7], 1⟩, ⟨209, [.column .advice 7], 1⟩, ⟨205, [.column .advice 7], 1⟩, ⟨89, [.column .advice 6], 1⟩, ⟨204, [.column .advice 7], 1⟩, ⟨201, [.column .advice 7], 1⟩, ⟨92, [.column .advice 6], 1⟩, ⟨93, [.column .advice 6], 1⟩, ⟨197, [.column .advice 7], 1⟩, ⟨196, [.column .advice 7], 1⟩, ⟨193, [.column .advice 7], 1⟩, ⟨97, [.column .advice 6], 1⟩, ⟨0, [.column .advice 0], 1⟩, ⟨189, [.column .advice 7], 1⟩, ⟨100, [.column .advice 6], 1⟩, ⟨101, [.column .advice 6], 1⟩, ⟨188, [.column .advice 7], 1⟩, ⟨185, [.column .advice 7], 1⟩, ⟨181, [.column .advice 7], 1⟩, ⟨105, [.column .advice 6], 1⟩, ⟨180, [.column .advice 7], 1⟩, ⟨177, [.column .advice 7], 1⟩, ⟨108, [.column .advice 6], 1⟩, ⟨109, [.column .advice 6], 1⟩, ⟨173, [.column .advice 7], 1⟩, ⟨172, [.column .advice 7], 1⟩, ⟨169, [.column .advice 7], 1⟩, ⟨113, [.column .advice 6], 1⟩, ⟨165, [.column .advice 7], 1⟩, ⟨164, [.column .advice 7], 1⟩, ⟨116, [.column .advice 6], 1⟩, ⟨117, [.column .advice 6], 1⟩, ⟨161, [.column .advice 7], 1⟩, ⟨157, [.column .advice 7], 1⟩, ⟨156, [.column .advice 7], 1⟩, ⟨121, [.column .advice 6], 1⟩, ⟨153, [.column .advice 7], 1⟩, ⟨149, [.column .advice 7], 1⟩, ⟨124, [.column .advice 6], 1⟩, ⟨125, [.column .advice 6], 1⟩, ⟨148, [.column .advice 7], 1⟩, ⟨301, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨347, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨348, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨4, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨3, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨2, [.selector 5, .column .advice 0, .column .advice 1], 1⟩]

def sortNode2Plan : Pdqsort.Plan :=
  .unary sortNode1Plan

def sortNode2Layer : Pdqsort.Layer RegionShape :=
  .unary #[⟨25, [.column .advice 6], 1⟩, ⟨6, [.column .advice 0], 1⟩, ⟨7, [.column .advice 0], 1⟩, ⟨364, [.column .advice 7], 1⟩, ⟨9, [.column .advice 6], 1⟩, ⟨362, [.column .advice 7], 1⟩, ⟨360, [.column .advice 7], 1⟩, ⟨12, [.column .advice 6], 1⟩, ⟨13, [.column .advice 6], 1⟩, ⟨359, [.column .advice 7], 1⟩, ⟨356, [.column .advice 7], 1⟩, ⟨354, [.column .advice 7], 1⟩, ⟨17, [.column .advice 6], 1⟩, ⟨353, [.column .advice 7], 1⟩, ⟨350, [.column .advice 7], 1⟩, ⟨20, [.column .advice 6], 1⟩, ⟨21, [.column .advice 6], 1⟩, ⟨349, [.column .advice 0], 1⟩, ⟨241, [.column .advice 7], 1⟩, ⟨132, [.column .advice 6], 1⟩, ⟨137, [.column .advice 7], 1⟩, ⟨140, [.column .advice 7], 1⟩, ⟨317, [.column .advice 6], 1⟩, ⟨28, [.column .advice 6], 1⟩, ⟨1, [.column .advice 0], 1⟩, ⟨315, [.column .advice 6], 1⟩, ⟨313, [.column .advice 6], 1⟩, ⟨312, [.column .advice 6], 1⟩, ⟨33, [.column .advice 6], 1⟩, ⟨309, [.column .advice 6], 1⟩, ⟨307, [.column .advice 6], 1⟩, ⟨36, [.column .advice 6], 1⟩, ⟨37, [.column .advice 6], 1⟩, ⟨306, [.column .advice 6], 1⟩, ⟨303, [.column .advice 6], 1⟩, ⟨133, [.column .advice 6], 1⟩, ⟨41, [.column .advice 6], 1⟩, ⟨129, [.column .advice 6], 1⟩, ⟨141, [.column .advice 7], 1⟩, ⟨145, [.column .advice 7], 1⟩, ⟨298, [.column .advice 6], 1⟩, ⟨44, [.column .advice 6], 1⟩, ⟨45, [.column .advice 6], 1⟩, ⟨289, [.column .advice 6], 1⟩, ⟨287, [.column .advice 6], 1⟩, ⟨286, [.column .advice 6], 1⟩, ⟨49, [.column .advice 6], 1⟩, ⟨283, [.column .advice 6], 1⟩, ⟨265, [.column .advice 9], 1⟩, ⟨52, [.column .advice 6], 1⟩, ⟨53, [.column .advice 6], 1⟩, ⟨264, [.column .advice 9], 1⟩, ⟨261, [.column .advice 7], 1⟩, ⟨260, [.column .advice 7], 1⟩, ⟨57, [.column .advice 6], 1⟩, ⟨257, [.column .advice 7], 1⟩, ⟨253, [.column .advice 7], 1⟩, ⟨60, [.column .advice 6], 1⟩, ⟨61, [.column .advice 6], 1⟩, ⟨252, [.column .advice 7], 1⟩, ⟨249, [.column .advice 7], 1⟩, ⟨245, [.column .advice 7], 1⟩, ⟨65, [.column .advice 6], 1⟩, ⟨29, [.column .advice 6], 1⟩, ⟨68, [.column .advice 6], 1⟩, ⟨5, [.column .advice 0], 1⟩, ⟨69, [.column .advice 6], 1⟩, ⟨237, [.column .advice 7], 1⟩, ⟨236, [.column .advice 7], 1⟩, ⟨233, [.column .advice 7], 1⟩, ⟨73, [.column .advice 6], 1⟩, ⟨229, [.column .advice 7], 1⟩, ⟨228, [.column .advice 7], 1⟩, ⟨76, [.column .advice 6], 1⟩, ⟨77, [.column .advice 6], 1⟩, ⟨225, [.column .advice 7], 1⟩, ⟨221, [.column .advice 7], 1⟩, ⟨220, [.column .advice 7], 1⟩, ⟨81, [.column .advice 6], 1⟩, ⟨217, [.column .advice 7], 1⟩, ⟨213, [.column .advice 7], 1⟩, ⟨84, [.column .advice 6], 1⟩, ⟨85, [.column .advice 6], 1⟩, ⟨212, [.column .advice 7], 1⟩, ⟨209, [.column .advice 7], 1⟩, ⟨205, [.column .advice 7], 1⟩, ⟨89, [.column .advice 6], 1⟩, ⟨204, [.column .advice 7], 1⟩, ⟨201, [.column .advice 7], 1⟩, ⟨92, [.column .advice 6], 1⟩, ⟨93, [.column .advice 6], 1⟩, ⟨197, [.column .advice 7], 1⟩, ⟨196, [.column .advice 7], 1⟩, ⟨193, [.column .advice 7], 1⟩, ⟨97, [.column .advice 6], 1⟩, ⟨0, [.column .advice 0], 1⟩, ⟨189, [.column .advice 7], 1⟩, ⟨100, [.column .advice 6], 1⟩, ⟨101, [.column .advice 6], 1⟩, ⟨188, [.column .advice 7], 1⟩, ⟨185, [.column .advice 7], 1⟩, ⟨181, [.column .advice 7], 1⟩, ⟨105, [.column .advice 6], 1⟩, ⟨180, [.column .advice 7], 1⟩, ⟨177, [.column .advice 7], 1⟩, ⟨108, [.column .advice 6], 1⟩, ⟨109, [.column .advice 6], 1⟩, ⟨173, [.column .advice 7], 1⟩, ⟨172, [.column .advice 7], 1⟩, ⟨169, [.column .advice 7], 1⟩, ⟨113, [.column .advice 6], 1⟩, ⟨165, [.column .advice 7], 1⟩, ⟨164, [.column .advice 7], 1⟩, ⟨116, [.column .advice 6], 1⟩, ⟨117, [.column .advice 6], 1⟩, ⟨161, [.column .advice 7], 1⟩, ⟨157, [.column .advice 7], 1⟩, ⟨156, [.column .advice 7], 1⟩, ⟨121, [.column .advice 6], 1⟩, ⟨153, [.column .advice 7], 1⟩, ⟨149, [.column .advice 7], 1⟩, ⟨124, [.column .advice 6], 1⟩, ⟨125, [.column .advice 6], 1⟩, ⟨148, [.column .advice 7], 1⟩] (⟨sortNode1Input, some ⟨244, [.column .advice 7], 1⟩, 8, false, false⟩)

set_option maxRecDepth 1000000 in
theorem sortNode2Layer_eq :
    Pdqsort.stepLayer sortNode2Input less (some ⟨244, [.column .advice 7], 1⟩)
      9 false false =
        sortNode2Layer := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sortNode2 :
    Pdqsort.recursePlanned 394 sortNode2Plan
      sortNode2Input less (some ⟨244, [.column .advice 7], 1⟩)
      9 false false =
        some sortNode2Output := by
  rw [Pdqsort.recursePlanned.eq_2,
    Pdqsort.recurseStepPlanned_eq_interpretLayer, sortNode2Layer_eq]
  simp only [Pdqsort.interpretLayer, sortNode2Layer,
    sortNode2Plan, sortNode1]
  all_goals decide +kernel

def sortNode3Input : Array RegionShape :=
  #[⟨133, [.column .advice 6], 1⟩, ⟨1, [.column .advice 0], 1⟩, ⟨2, [.selector 5, .column .advice 0, .column .advice 1], 1⟩, ⟨3, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨4, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨5, [.column .advice 0], 1⟩, ⟨6, [.column .advice 0], 1⟩, ⟨7, [.column .advice 0], 1⟩, ⟨364, [.column .advice 7], 1⟩, ⟨9, [.column .advice 6], 1⟩, ⟨362, [.column .advice 7], 1⟩, ⟨360, [.column .advice 7], 1⟩, ⟨12, [.column .advice 6], 1⟩, ⟨13, [.column .advice 6], 1⟩, ⟨359, [.column .advice 7], 1⟩, ⟨356, [.column .advice 7], 1⟩, ⟨354, [.column .advice 7], 1⟩, ⟨17, [.column .advice 6], 1⟩, ⟨353, [.column .advice 7], 1⟩, ⟨350, [.column .advice 7], 1⟩, ⟨20, [.column .advice 6], 1⟩, ⟨21, [.column .advice 6], 1⟩, ⟨349, [.column .advice 0], 1⟩, ⟨348, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨347, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨25, [.column .advice 6], 1⟩, ⟨346, [], 0⟩, ⟨317, [.column .advice 6], 1⟩, ⟨28, [.column .advice 6], 1⟩, ⟨29, [.column .advice 6], 1⟩, ⟨315, [.column .advice 6], 1⟩, ⟨313, [.column .advice 6], 1⟩, ⟨312, [.column .advice 6], 1⟩, ⟨33, [.column .advice 6], 1⟩, ⟨309, [.column .advice 6], 1⟩, ⟨307, [.column .advice 6], 1⟩, ⟨36, [.column .advice 6], 1⟩, ⟨37, [.column .advice 6], 1⟩, ⟨306, [.column .advice 6], 1⟩, ⟨303, [.column .advice 6], 1⟩, ⟨302, [], 0⟩, ⟨41, [.column .advice 6], 1⟩, ⟨301, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨298, [.column .advice 6], 1⟩, ⟨44, [.column .advice 6], 1⟩, ⟨45, [.column .advice 6], 1⟩, ⟨289, [.column .advice 6], 1⟩, ⟨287, [.column .advice 6], 1⟩, ⟨286, [.column .advice 6], 1⟩, ⟨49, [.column .advice 6], 1⟩, ⟨283, [.column .advice 6], 1⟩, ⟨265, [.column .advice 9], 1⟩, ⟨52, [.column .advice 6], 1⟩, ⟨53, [.column .advice 6], 1⟩, ⟨264, [.column .advice 9], 1⟩, ⟨261, [.column .advice 7], 1⟩, ⟨260, [.column .advice 7], 1⟩, ⟨57, [.column .advice 6], 1⟩, ⟨257, [.column .advice 7], 1⟩, ⟨253, [.column .advice 7], 1⟩, ⟨60, [.column .advice 6], 1⟩, ⟨61, [.column .advice 6], 1⟩, ⟨252, [.column .advice 7], 1⟩, ⟨249, [.column .advice 7], 1⟩, ⟨245, [.column .advice 7], 1⟩, ⟨65, [.column .advice 6], 1⟩, ⟨244, [.column .advice 7], 1⟩, ⟨241, [.column .advice 7], 1⟩, ⟨68, [.column .advice 6], 1⟩, ⟨69, [.column .advice 6], 1⟩, ⟨237, [.column .advice 7], 1⟩, ⟨236, [.column .advice 7], 1⟩, ⟨233, [.column .advice 7], 1⟩, ⟨73, [.column .advice 6], 1⟩, ⟨229, [.column .advice 7], 1⟩, ⟨228, [.column .advice 7], 1⟩, ⟨76, [.column .advice 6], 1⟩, ⟨77, [.column .advice 6], 1⟩, ⟨225, [.column .advice 7], 1⟩, ⟨221, [.column .advice 7], 1⟩, ⟨220, [.column .advice 7], 1⟩, ⟨81, [.column .advice 6], 1⟩, ⟨217, [.column .advice 7], 1⟩, ⟨213, [.column .advice 7], 1⟩, ⟨84, [.column .advice 6], 1⟩, ⟨85, [.column .advice 6], 1⟩, ⟨212, [.column .advice 7], 1⟩, ⟨209, [.column .advice 7], 1⟩, ⟨205, [.column .advice 7], 1⟩, ⟨89, [.column .advice 6], 1⟩, ⟨204, [.column .advice 7], 1⟩, ⟨201, [.column .advice 7], 1⟩, ⟨92, [.column .advice 6], 1⟩, ⟨93, [.column .advice 6], 1⟩, ⟨197, [.column .advice 7], 1⟩, ⟨196, [.column .advice 7], 1⟩, ⟨193, [.column .advice 7], 1⟩, ⟨97, [.column .advice 6], 1⟩, ⟨0, [.column .advice 0], 1⟩, ⟨189, [.column .advice 7], 1⟩, ⟨100, [.column .advice 6], 1⟩, ⟨101, [.column .advice 6], 1⟩, ⟨188, [.column .advice 7], 1⟩, ⟨185, [.column .advice 7], 1⟩, ⟨181, [.column .advice 7], 1⟩, ⟨105, [.column .advice 6], 1⟩, ⟨180, [.column .advice 7], 1⟩, ⟨177, [.column .advice 7], 1⟩, ⟨108, [.column .advice 6], 1⟩, ⟨109, [.column .advice 6], 1⟩, ⟨173, [.column .advice 7], 1⟩, ⟨172, [.column .advice 7], 1⟩, ⟨169, [.column .advice 7], 1⟩, ⟨113, [.column .advice 6], 1⟩, ⟨165, [.column .advice 7], 1⟩, ⟨164, [.column .advice 7], 1⟩, ⟨116, [.column .advice 6], 1⟩, ⟨117, [.column .advice 6], 1⟩, ⟨161, [.column .advice 7], 1⟩, ⟨157, [.column .advice 7], 1⟩, ⟨156, [.column .advice 7], 1⟩, ⟨121, [.column .advice 6], 1⟩, ⟨153, [.column .advice 7], 1⟩, ⟨149, [.column .advice 7], 1⟩, ⟨124, [.column .advice 6], 1⟩, ⟨125, [.column .advice 6], 1⟩, ⟨148, [.column .advice 7], 1⟩, ⟨145, [.column .advice 7], 1⟩, ⟨141, [.column .advice 7], 1⟩, ⟨129, [.column .advice 6], 1⟩, ⟨140, [.column .advice 7], 1⟩, ⟨137, [.column .advice 7], 1⟩, ⟨132, [.column .advice 6], 1⟩]

def sortNode3Output : Array RegionShape :=
  #[⟨302, [], 0⟩, ⟨346, [], 0⟩, ⟨244, [.column .advice 7], 1⟩, ⟨25, [.column .advice 6], 1⟩, ⟨6, [.column .advice 0], 1⟩, ⟨7, [.column .advice 0], 1⟩, ⟨364, [.column .advice 7], 1⟩, ⟨9, [.column .advice 6], 1⟩, ⟨362, [.column .advice 7], 1⟩, ⟨360, [.column .advice 7], 1⟩, ⟨12, [.column .advice 6], 1⟩, ⟨13, [.column .advice 6], 1⟩, ⟨359, [.column .advice 7], 1⟩, ⟨356, [.column .advice 7], 1⟩, ⟨354, [.column .advice 7], 1⟩, ⟨17, [.column .advice 6], 1⟩, ⟨353, [.column .advice 7], 1⟩, ⟨350, [.column .advice 7], 1⟩, ⟨20, [.column .advice 6], 1⟩, ⟨21, [.column .advice 6], 1⟩, ⟨349, [.column .advice 0], 1⟩, ⟨241, [.column .advice 7], 1⟩, ⟨132, [.column .advice 6], 1⟩, ⟨137, [.column .advice 7], 1⟩, ⟨140, [.column .advice 7], 1⟩, ⟨317, [.column .advice 6], 1⟩, ⟨28, [.column .advice 6], 1⟩, ⟨1, [.column .advice 0], 1⟩, ⟨315, [.column .advice 6], 1⟩, ⟨313, [.column .advice 6], 1⟩, ⟨312, [.column .advice 6], 1⟩, ⟨33, [.column .advice 6], 1⟩, ⟨309, [.column .advice 6], 1⟩, ⟨307, [.column .advice 6], 1⟩, ⟨36, [.column .advice 6], 1⟩, ⟨37, [.column .advice 6], 1⟩, ⟨306, [.column .advice 6], 1⟩, ⟨303, [.column .advice 6], 1⟩, ⟨133, [.column .advice 6], 1⟩, ⟨41, [.column .advice 6], 1⟩, ⟨129, [.column .advice 6], 1⟩, ⟨141, [.column .advice 7], 1⟩, ⟨145, [.column .advice 7], 1⟩, ⟨298, [.column .advice 6], 1⟩, ⟨44, [.column .advice 6], 1⟩, ⟨45, [.column .advice 6], 1⟩, ⟨289, [.column .advice 6], 1⟩, ⟨287, [.column .advice 6], 1⟩, ⟨286, [.column .advice 6], 1⟩, ⟨49, [.column .advice 6], 1⟩, ⟨283, [.column .advice 6], 1⟩, ⟨265, [.column .advice 9], 1⟩, ⟨52, [.column .advice 6], 1⟩, ⟨53, [.column .advice 6], 1⟩, ⟨264, [.column .advice 9], 1⟩, ⟨261, [.column .advice 7], 1⟩, ⟨260, [.column .advice 7], 1⟩, ⟨57, [.column .advice 6], 1⟩, ⟨257, [.column .advice 7], 1⟩, ⟨253, [.column .advice 7], 1⟩, ⟨60, [.column .advice 6], 1⟩, ⟨61, [.column .advice 6], 1⟩, ⟨252, [.column .advice 7], 1⟩, ⟨249, [.column .advice 7], 1⟩, ⟨245, [.column .advice 7], 1⟩, ⟨65, [.column .advice 6], 1⟩, ⟨29, [.column .advice 6], 1⟩, ⟨68, [.column .advice 6], 1⟩, ⟨5, [.column .advice 0], 1⟩, ⟨69, [.column .advice 6], 1⟩, ⟨237, [.column .advice 7], 1⟩, ⟨236, [.column .advice 7], 1⟩, ⟨233, [.column .advice 7], 1⟩, ⟨73, [.column .advice 6], 1⟩, ⟨229, [.column .advice 7], 1⟩, ⟨228, [.column .advice 7], 1⟩, ⟨76, [.column .advice 6], 1⟩, ⟨77, [.column .advice 6], 1⟩, ⟨225, [.column .advice 7], 1⟩, ⟨221, [.column .advice 7], 1⟩, ⟨220, [.column .advice 7], 1⟩, ⟨81, [.column .advice 6], 1⟩, ⟨217, [.column .advice 7], 1⟩, ⟨213, [.column .advice 7], 1⟩, ⟨84, [.column .advice 6], 1⟩, ⟨85, [.column .advice 6], 1⟩, ⟨212, [.column .advice 7], 1⟩, ⟨209, [.column .advice 7], 1⟩, ⟨205, [.column .advice 7], 1⟩, ⟨89, [.column .advice 6], 1⟩, ⟨204, [.column .advice 7], 1⟩, ⟨201, [.column .advice 7], 1⟩, ⟨92, [.column .advice 6], 1⟩, ⟨93, [.column .advice 6], 1⟩, ⟨197, [.column .advice 7], 1⟩, ⟨196, [.column .advice 7], 1⟩, ⟨193, [.column .advice 7], 1⟩, ⟨97, [.column .advice 6], 1⟩, ⟨0, [.column .advice 0], 1⟩, ⟨189, [.column .advice 7], 1⟩, ⟨100, [.column .advice 6], 1⟩, ⟨101, [.column .advice 6], 1⟩, ⟨188, [.column .advice 7], 1⟩, ⟨185, [.column .advice 7], 1⟩, ⟨181, [.column .advice 7], 1⟩, ⟨105, [.column .advice 6], 1⟩, ⟨180, [.column .advice 7], 1⟩, ⟨177, [.column .advice 7], 1⟩, ⟨108, [.column .advice 6], 1⟩, ⟨109, [.column .advice 6], 1⟩, ⟨173, [.column .advice 7], 1⟩, ⟨172, [.column .advice 7], 1⟩, ⟨169, [.column .advice 7], 1⟩, ⟨113, [.column .advice 6], 1⟩, ⟨165, [.column .advice 7], 1⟩, ⟨164, [.column .advice 7], 1⟩, ⟨116, [.column .advice 6], 1⟩, ⟨117, [.column .advice 6], 1⟩, ⟨161, [.column .advice 7], 1⟩, ⟨157, [.column .advice 7], 1⟩, ⟨156, [.column .advice 7], 1⟩, ⟨121, [.column .advice 6], 1⟩, ⟨153, [.column .advice 7], 1⟩, ⟨149, [.column .advice 7], 1⟩, ⟨124, [.column .advice 6], 1⟩, ⟨125, [.column .advice 6], 1⟩, ⟨148, [.column .advice 7], 1⟩, ⟨301, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨347, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨348, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨4, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨3, [.selector 6, .column .advice 0, .column .advice 1], 1⟩, ⟨2, [.selector 5, .column .advice 0, .column .advice 1], 1⟩]

def sortNode3Plan : Pdqsort.Plan :=
  .binary sortNode0Plan sortNode2Plan

def sortNode3Layer : Pdqsort.Layer RegionShape :=
  .binary (⟨sortNode0Input, none, 9, true, true⟩) ⟨244, [.column .advice 7], 1⟩ (⟨sortNode2Input, some ⟨244, [.column .advice 7], 1⟩, 9, false, false⟩)

set_option maxRecDepth 1000000 in
theorem sortNode3Layer_eq :
    Pdqsort.stepLayer sortNode3Input less (none)
      9 true true =
        sortNode3Layer := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sortNode3 :
    Pdqsort.recursePlanned 395 sortNode3Plan
      sortNode3Input less (none)
      9 true true =
        some sortNode3Output := by
  rw [Pdqsort.recursePlanned.eq_2,
    Pdqsort.recurseStepPlanned_eq_interpretLayer, sortNode3Layer_eq]
  simp only [Pdqsort.interpretLayer, sortNode3Layer,
    sortNode3Plan, sortNode0, sortNode2]
  all_goals decide +kernel

end Zcash.Circuits.Action.PlannerSort
