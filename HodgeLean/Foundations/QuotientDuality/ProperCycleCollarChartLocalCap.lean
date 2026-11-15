import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRestrictedPointIso

/-! # Actual local support caps in the original flattened chart
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Pullback along actual collar chart coordinates, capped on the literal smaller collar triad with the specified ambient point class, and pushed by the actual retraction into support point homology.
Source: triadCapCohomologyLinear; ProperCycleSupportCollar.chart_support_point_pair; ProperCycleSupportCollar.restricted_point_triad_iso.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.chart_local_support_cap
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p q : ℕ)
    (c : orientationGroup (TopCat.of W) (p+q) ⟨z.val, hzW⟩) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' {y}ᶜ)) p →ₗ[ℚ]
      orientationGroup (TopCat.of {s : S | s.val ∈ e.source}) q ⟨z, hWe hzW⟩ :=
  (relativeHomologyMap ℚ q (C.chart_support_point_pair e W hWe hWN hR z hzW)).comp
    (((triadCapCohomologyLinear ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) p q).flip
      ((C.restricted_point_triad_iso hS W hWN z hzW (p+q)).inv.hom c)).comp
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom
          (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter))
          (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1)))

end HodgeLean.Foundations.QuotientDuality
