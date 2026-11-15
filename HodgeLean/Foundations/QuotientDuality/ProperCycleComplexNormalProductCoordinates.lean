import HodgeLean.Foundations.QuotientDuality.ProperCycleMixedComplexRealCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportCoclass
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSupportIntersections

/-! # Actual complex product coordinates on the iterated normal support model
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual recursive real product coordinates followed by the specified inverse consecutive complex tangential coordinates.
Source: properCycle_real_support_coordinates; AlgebraicTopology.Singular.complexRealHomeomorph.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_product_coordinates (r d : ℕ) :
    properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2) ≃ₜ
      ((Fin r → ℂ) × (Fin d → ℂ)) :=
  (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) (r*2)).trans
    ((complexRealHomeomorph r).symm.prodCongr (Homeomorph.refl (Fin d → ℂ)))

/-- The actual complex product coordinates retain the original normal support as the literal inverse image under the normal projection.
Source: properCycle_real_support_coordinates_normal; properCycle_complex_normal_product_coordinates.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_product_coordinates_normal (r d : ℕ) :
    (properCycle_complex_normal_product_coordinates r d) ⁻¹'
      (Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))) =
      properCycle_real_normal_support (TopCat.of (Fin d → ℂ)) {0} (r*2) := by
  exact properCycle_real_support_coordinates_normal (TopCat.of (Fin d → ℂ)) {0} (r*2)

/-- The actual complex product coordinates retain the original recursive tangential point support as the literal tangential zero slice.
Source: properCycle_real_support_coordinates_point; Complex.piCoordCLE.map_eq_zero_iff.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_product_coordinates_point (r d : ℕ) :
    (properCycle_complex_normal_product_coordinates r d) ⁻¹'
      {z : (Fin r → ℂ) × (Fin d → ℂ) | z.1 = 0} =
      properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ (r*2) := by
  ext z
  have h := Set.ext_iff.mp (properCycle_real_support_coordinates_point
    (TopCat.of (Fin d → ℂ)) Set.univ (r*2)) z
  change ((properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) (r*2) z).1 = 0 ∧ True) ↔
    z ∈ properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ (r*2) at h
  simp only [and_true] at h
  change (Complex.piCoordCLE r).symm
    (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) (r*2) z).1 = 0 ↔ _
  exact (ContinuousLinearEquiv.map_eq_zero_iff (Complex.piCoordCLE r).symm).trans h

/-- The actual complex product origin is precisely the specified recursive normal and tangential support intersection.
Source: properCycle_complex_normal_product_coordinates_normal; properCycle_complex_normal_product_coordinates_point; properCycle_iterated_support_intersection.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_product_coordinates_origin (r d : ℕ) :
    (properCycle_complex_normal_product_coordinates r d) ⁻¹'
      ({(0,0)} : Set ((Fin r → ℂ) × (Fin d → ℂ))) =
      properCycle_real_point_support (TopCat.of (Fin d → ℂ))
        (({0} : Set (Fin d → ℂ)) ∩ Set.univ) (r*2) := by
  ext z
  let e := properCycle_complex_normal_product_coordinates r d
  have hn := Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_normal r d) z
  have ht := Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_point r d) z
  have hi := Set.ext_iff.mp (properCycle_iterated_support_intersection
    (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)) z
  change (e z).2 = 0 ↔ z ∈ properCycle_real_normal_support (TopCat.of (Fin d → ℂ)) {0} (r*2) at hn
  change (e z).1 = 0 ↔ z ∈ properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ (r*2) at ht
  change e z = (0,0) ↔ _
  rw [Prod.ext_iff, ht, hn]
  exact and_comm.trans hi

end HodgeLean.Foundations.QuotientDuality
