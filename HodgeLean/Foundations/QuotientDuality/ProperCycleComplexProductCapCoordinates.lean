import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalCoclassComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedUnionRelativeCap

/-! # Original product cap through actual complex support coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual complex coordinate map on ordinary normal and tangential intersection-support pairs, retaining the original complement-union maps.
Source: properCycle_support_intersection_pair_map; properCycle_complex_normal_product_coordinates_normal; properCycle_complex_normal_product_coordinates_point.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_product_intersection_pair_map (r d : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2))
      (properCycle_real_normal_support (TopCat.of (Fin d → ℂ)) {0} (r*2) ∩
        properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ (r*2))ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ)))
        ((Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))) ∩ {z | z.1 = 0})ᶜ :=
  properCycle_support_intersection_pair_map
    (TopCat.ofHom ⟨properCycle_complex_normal_product_coordinates r d,
      (properCycle_complex_normal_product_coordinates r d).continuous⟩)
    _ _ _ _
    (fun z hz hu => hz ((Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_normal r d) z).mp hu))
    (fun z hz hv => hz ((Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_point r d) z).mp hv))

/-- The original iterated normal cap is carried to the original ordinary complex product cap by the same actual support-coordinate maps and original normal coclass pullback.
Source: properCycle_support_cap_naturality; properCycle_complex_normal_coclass_pullback; properCycle_iterated_union_relative_cap.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_product_cap_coordinate_square (r d p : ℕ)
    (a : RelativeCohomology ℚ (puncturedPair ℂ d) p)
    (z : RelativeHomology ℚ
      (TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2))
        (properCycle_real_point_support (TopCat.of (Fin d → ℂ))
          (({0} : Set (Fin d → ℂ)) ∩ Set.univ) (r*2))ᶜ) (p+r*2)) :
    let Y := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))
    let U : Set Y := Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))
    let V : Set Y := {z | z.1 = 0}
    relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_product_tangent_pair_iso r d).hom
      ((properCycle_iterated_union_relative_cap (TopCat.of (Fin d → ℂ)) {0} Set.univ
        isClosed_singleton isClosed_univ p a (r*2)).hom z) =
      (properCycle_union_relative_support_cap Y U V (isClosed_singleton.preimage continuous_snd)
        (isClosed_eq continuous_fst continuous_const) p (r*2)
        (relativeCohomologyMap ℚ p
          (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0}) a)).hom
        (relativeHomologyMap ℚ (p+r*2)
          ((properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv ≫
            properCycle_complex_normal_product_intersection_pair_map r d) z) := by
  let X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2)
  let Y := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))
  let S := properCycle_real_normal_support (TopCat.of (Fin d → ℂ)) {0} (r*2)
  let T := properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ (r*2)
  let U : Set Y := Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))
  let V : Set Y := {z | z.1 = 0}
  let f : X ⟶ Y := TopCat.ofHom ⟨properCycle_complex_normal_product_coordinates r d,
    (properCycle_complex_normal_product_coordinates r d).continuous⟩
  let hA : Set.MapsTo f Sᶜ Uᶜ := fun z hz hu =>
    hz ((Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_normal r d) z).mp hu)
  let hB : Set.MapsTo f Tᶜ Vᶜ := fun z hz hv =>
    hz ((Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_point r d) z).mp hv)
  let hS := properCycle_real_normal_support_isClosed (TopCat.of (Fin d → ℂ)) {0} isClosed_singleton (r*2)
  let hT := properCycle_real_point_support_isClosed (TopCat.of (Fin d → ℂ)) Set.univ isClosed_univ (r*2)
  let hU : IsClosed U := isClosed_singleton.preimage continuous_snd
  let hV : IsClosed V := isClosed_eq continuous_fst continuous_const
  let b := relativeCohomologyMap ℚ p
    (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0}) a
  have hA' : TopPair.ofSubsetHom f hA = (properCycle_complex_normal_product_normal_pair_iso r d).hom := by
    ext x : 2 <;> rfl
  have hB' : TopPair.ofSubsetHom f hB = (properCycle_complex_normal_product_tangent_pair_iso r d).hom := by
    ext x : 2 <;> rfl
  have hn := properCycle_support_cap_naturality f S T U V hA hB hS hT hU hV p (r*2) b
    (relativeHomologyMap ℚ (p+r*2)
      (properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv z)
  have hab : relativeCohomologyMap ℚ p (properCycle_complex_normal_product_normal_pair_iso r d).hom b =
      properCycle_real_support_coclass (TopCat.of (Fin d → ℂ)) {0} p a (r*2) :=
    properCycle_complex_normal_coclass_pullback r d p a
  rw [hA', hB'] at hn
  erw [hab] at hn
  change relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_product_tangent_pair_iso r d).hom
      ((properCycle_iterated_union_relative_cap (TopCat.of (Fin d → ℂ)) {0} Set.univ
        isClosed_singleton isClosed_univ p a (r*2)).hom z) =
    (properCycle_union_relative_support_cap Y U V hU hV p (r*2) b).hom
      (relativeHomologyMap ℚ (p+r*2) (properCycle_complex_normal_product_intersection_pair_map r d)
        (relativeHomologyMap ℚ (p+r*2)
          (properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv z)) at hn
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply]
  exact hn

end HodgeLean.Foundations.QuotientDuality
