import HodgeLean.Foundations.Program.SchoenTransferQ3NormalCoclassGeneration
import HodgeLean.RealDefs.DegreeZero

/-! Detection of ambient supported coclasses on arbitrarily small normal slices. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- A normal-coordinate slice detects the ambient flattened coclass even
when its neighbourhood has a different radius from the ambient one. -/
theorem s4_q3_small_normal_slice_pullback_injective
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)
    (V : Set N) (hV : V ⊆ d.source) (hVo : IsOpen V)
    (z : N) (hz : z ∈ V) (hz0 : (d z).2 = 0)
    (φ : neighborhoodSupportComplementPair V T ⟶
      neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S)
    (hnormal : ∀ y : V, (e (TopPair.Hom.fst φ y).1).2 = (d y.1).2) :
    Function.Injective (relativeCohomologyMap ℚ (2 * c) φ) := by
  have htransport := s4_q3_normal_coclass_pullback F E c d e T S hT hS V
    (flattenedSupportNeighborhood E c e x hx) hV
    (flattenedSupportNeighborhood_subset_source E c e x hx) φ hnormal
  have hne := chartNormalProjectionCoclass_ne_zero F c d T hT hVo hV hz hz0
  intro α β hab
  have hα := s4_q3_normal_coclass_coefficient E c e S hS x hx h0 α
  have hβ := s4_q3_normal_coclass_coefficient E c e S hS x hx h0 β
  rw [hα, hβ, map_smul, map_smul, htransport] at hab
  have hc := smul_left_injective ℚ hne hab
  rw [hα, hβ, hc]

end HodgeLean.Foundations.Program
