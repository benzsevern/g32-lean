import HodgeLean.Foundations.BundleResolution.ChernRelativeCupCochainHelpers

/-! # Actual relative singular cohomology cup action

Duality with the actual same-pair relative cap product descends the cup
action to the specified rational singular cohomology objects.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (p q : ℕ)

def i1_relativeCup :
    RelativeCohomology ℚ P p →ₗ[ℚ]
      Cohomology ℚ P.fst q →ₗ[ℚ] RelativeCohomology ℚ P (p + q) where
  toFun α := (relativeCohomologyEquivDualHomology ℚ P (p + q)).symm.toLinearMap.comp
    (((relativeCapCohomologyLinear ℚ P p q α).dualMap).comp
      (cohomologyEquivDualHomology ℚ P.fst q).toLinearMap)
  map_add' α β := by
    ext γ
    apply (relativeCohomologyEquivDualHomology ℚ P (p + q)).injective
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      map_add, LinearMap.add_apply, LinearMap.dualMap_apply]
  map_smul' a α := by
    ext γ
    apply (relativeCohomologyEquivDualHomology ℚ P (p + q)).injective
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      map_smul, LinearMap.smul_apply, LinearMap.dualMap_apply, RingHom.id_apply]

theorem i1_relativeCup_pairing (α : RelativeCohomology ℚ P p)
    (β : Cohomology ℚ P.fst q) (z : RelativeHomology ℚ P (p + q)) :
    relativeCohomologyEquivDualHomology ℚ P (p + q) (i1_relativeCup P p q α β) z =
      cohomologyEquivDualHomology ℚ P.fst q β (relativeCapCohomologyLinear ℚ P p q α z) := by
  exact congrArg (fun f => f z)
    ((relativeCohomologyEquivDualHomology ℚ P (p + q)).apply_symm_apply _)

theorem i1_relativeCup_injective_of_cap_surjective (α : RelativeCohomology ℚ P p)
    (hcap : Function.Surjective (relativeCapCohomologyLinear ℚ P p q α)) :
    Function.Injective (i1_relativeCup P p q α) :=
  (relativeCohomologyEquivDualHomology ℚ P (p + q)).symm.injective.comp
    ((LinearMap.dualMap_injective_of_surjective hcap).comp
      (cohomologyEquivDualHomology ℚ P.fst q).injective)

theorem i1_relativeCup_bijective_of_cap_bijective (α : RelativeCohomology ℚ P p)
    (hcap : Function.Bijective (relativeCapCohomologyLinear ℚ P p q α)) :
    Function.Bijective (i1_relativeCup P p q α) := by
  have hd : Function.Bijective (relativeCapCohomologyLinear ℚ P p q α).dualMap :=
    (LinearEquiv.ofBijective _ hcap).dualMap.bijective
  exact (relativeCohomologyEquivDualHomology ℚ P (p + q)).symm.bijective.comp
    (hd.comp (cohomologyEquivDualHomology ℚ P.fst q).bijective)

end HodgeLean.Foundations.BundleResolution
