import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartLocalDuality
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenOrientationGenerator

/-! # Actual collar chart duality with the specified global ambient class
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart cap is bijective with the specified global ambient class restricted by original point excision.
Source: ProperCycleSupportCollar.chart_local_support_cap_bijective; properCycle_open_orientation_generator.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_ambient_local_support_cap_bijective
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] [ContractibleSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p : ℕ) (hp : Even p)
    (c : Homology ℚ X (p + Module.finrank ℝ E))
    (hc : Function.Bijective (orientationLine X (p + Module.finrank ℝ E) c z.val)) :
    Function.Bijective (C.chart_local_support_cap hS E Y e W hWe hWN hR y hflat z hzW hcenter
      p (Module.finrank ℝ E)
      ((properCycle_open_local_homology_iso X W ⟨z.val, hzW⟩
        (p + Module.finrank ℝ E)).inv.hom
        (localOrientation X (p + Module.finrank ℝ E) c z.val))) := by
  exact C.chart_local_support_cap_bijective hS E Y e W hWe hWN hR y hflat z hzW hcenter p hp _
    (properCycle_open_orientation_generator X W ⟨z.val, hzW⟩ _ c hc)

end HodgeLean.Foundations.QuotientDuality
