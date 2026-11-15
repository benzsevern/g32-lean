import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # The exact zero-support equation near a fixed zero section

Injectivity of a local inverse identifies all preimages of nearby zero-section points.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.TubularEuler

theorem localInverse_zero_support_shrinking {B N : Type*}
    [TopologicalSpace B] [TopologicalSpace N] [Zero N]
    (L : OpenPartialHomeomorph (B × N) (B × N))
    (hzero : ∀ b, (b, (0 : N)) ∈ L.source → L (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ L.source) :
    ∃ U : Opens (B × N), (x, (0 : N)) ∈ U ∧
      (U : Set (B × N)) ⊆ L.source ∧
      ∀ z ∈ U, (L z).2 = 0 ↔ z.2 = 0 := by
  let Z : B × N → B × N := fun z => (z.1, 0)
  have hZ : Continuous Z := continuous_fst.prodMk continuous_const
  let U : Opens (B × N) := ⟨L.source ∩ L ⁻¹' (Z ⁻¹' L.source),
    L.isOpen_inter_preimage (L.open_source.preimage hZ)⟩
  refine ⟨U, ?_, fun _ h => h.1, ?_⟩
  · refine ⟨hx, ?_⟩
    change ((L (x, 0)).1, (0 : N)) ∈ L.source
    rw [hzero x hx]
    exact hx
  · intro z hz
    constructor
    · intro hn
      have hw : ((L z).1, (0 : N)) ∈ L.source := hz.2
      have hImage : L z = ((L z).1, (0 : N)) := Prod.ext rfl hn
      have heq : z = ((L z).1, (0 : N)) := L.injOn hz.1 hw
        (hImage.trans (hzero (L z).1 hw).symm)
      exact congrArg Prod.snd heq
    · intro hn
      have heq : z = (z.1, (0 : N)) := Prod.ext rfl hn
      have hw : (z.1, (0 : N)) ∈ L.source := heq ▸ hz.1
      exact (congrArg (fun w => (L w).2) heq).trans
        (congrArg Prod.snd (hzero z.1 hw))

#print axioms localInverse_zero_support_shrinking

end HodgeLean.Foundations.TubularEuler
