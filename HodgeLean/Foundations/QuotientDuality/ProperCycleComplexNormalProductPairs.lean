import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalProductCoordinates

/-! # Actual support-relative pair coordinates in the original complex product
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual complex product coordinate map on the original normal support-complement pairs.
Source: properCycle_complex_normal_product_coordinates_normal; AlgebraicTopology.Singular.TopPair.isoOfSubset.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_product_normal_pair_iso (r d : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2))
      (properCycle_real_normal_support (TopCat.of (Fin d → ℂ)) {0} (r*2))ᶜ ≅
      TopPair.ofSubset (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ)))
        (Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))ᶜ) :=
  TopPair.isoOfSubset (properCycle_complex_normal_product_coordinates r d)
    (fun z => not_congr (Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_normal r d) z))

/-- The same actual complex product coordinate map identifies the original recursive tangential support-complement pair with the literal product tangential pair.
Source: properCycle_complex_normal_product_coordinates_point; AlgebraicTopology.Singular.TopPair.isoOfSubset.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_product_tangent_pair_iso (r d : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2))
      (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ (r*2))ᶜ ≅
      TopPair.ofSubset (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) {z | z.1 = 0}ᶜ :=
  TopPair.isoOfSubset (properCycle_complex_normal_product_coordinates r d)
    (fun z => not_congr (Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_point r d) z))

/-- The actual complex product point-pair coordinates retain the specified recursive normal and tangential intersection source.
Source: properCycle_complex_normal_product_coordinates_origin; AlgebraicTopology.Singular.TopPair.isoOfSubset.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_product_point_pair_iso (r d : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) (r*2))
      (properCycle_real_point_support (TopCat.of (Fin d → ℂ))
        (({0} : Set (Fin d → ℂ)) ∩ Set.univ) (r*2))ᶜ ≅
      TopPair.ofSubset (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ)))
        ({(0,0)} : Set ((Fin r → ℂ) × (Fin d → ℂ)))ᶜ :=
  TopPair.isoOfSubset (properCycle_complex_normal_product_coordinates r d)
    (fun z => not_congr (Set.ext_iff.mp (properCycle_complex_normal_product_coordinates_origin r d) z))

end HodgeLean.Foundations.QuotientDuality
