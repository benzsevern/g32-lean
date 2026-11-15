import HodgeLean.Foundations.QuotientDuality.ProperCycleProductTangentHomology

/-! # The original normal cap from ambient to intrinsic local homology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original projected standard normal cap, through actual ambient excision and intrinsic tangential contraction, with its original complex ambient degree.
Source: Hatcher, Algebraic Topology, section 3.3, local complex cap duality.
HC no distance; AV milestone no distance. -/
def properCycle_standard_complex_local_cap (r d : ℕ) :
    orientationGroup (TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (2 * (r + d)) (0, 0) →ₗ[ℚ]
      orientationGroup (TopCat.of (Fin r → ℂ)) (2 * r) 0 := by
  let E := Fin r → ℂ
  let F := Fin d → ℂ
  let X := TopCat.of (E × F)
  let eN : orientationGroup X (2 * (r + d)) (0, 0) ≅
      orientationGroup X (2 * d + 2 * r) (0, 0) :=
    eqToIso (congrArg (fun n => orientationGroup X n (0, 0)) (by omega))
  let eS := properCycle_product_triad_local_homology_iso E F (2 * d + 2 * r)
  let eT := properCycle_product_tangent_local_homology_iso E F (2 * r)
  let a := relativeCohomologyMap ℚ (2 * d)
    (properCycle_product_support_projection E (TopCat.of F) {0})
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
      (standardComplexLocalClass_ne_zero_for_chart d))
  exact eT.hom.hom.comp ((triadCapCohomologyLinear ℚ X
    (Prod.snd ⁻¹' ({0} : Set F)ᶜ) {z | z.1 = 0}ᶜ (2 * d) (2 * r) a).comp
      (eS.inv.hom.comp eN.hom.hom))

/-- The original normal cap from actual ambient local homology to actual intrinsic tangential local homology is bijective.
Source: Hatcher, Algebraic Topology, section 3.3, local complex cap duality.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_complex_local_cap_bijective (r d : ℕ) :
    Function.Bijective (properCycle_standard_complex_local_cap r d) := by
  unfold properCycle_standard_complex_local_cap
  let X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))
  let eN : orientationGroup X (2 * (r + d)) (0, 0) ≅
      orientationGroup X (2 * d + 2 * r) (0, 0) :=
    eqToIso (congrArg (fun n => orientationGroup X n (0, 0)) (by omega))
  exact (ConcreteCategory.bijective_of_isIso
      (properCycle_product_tangent_local_homology_iso (Fin r → ℂ) (Fin d → ℂ) (2 * r)).hom).comp
    ((properCycle_standard_complex_product_triad_cap_bijective r d).comp
      ((ConcreteCategory.bijective_of_isIso
        (properCycle_product_triad_local_homology_iso (Fin r → ℂ) (Fin d → ℂ) (2 * d + 2 * r)).inv).comp
        (ConcreteCategory.bijective_of_isIso eN.hom)))

end HodgeLean.Foundations.QuotientDuality
