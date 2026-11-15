import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! # Actual dual-cycle representatives and their evaluation

The canonical short-complex comparison gives representatives of cohomology
in a linear-dual chain complex without choices of a cohomology basis.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

attribute [local implicit_reducible] ShortComplex.moduleCatMk

variable (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)

def i1_chainDualCycleClass :
    LinearMap.ker (K.sc n).f.hom.dualMap →ₗ[ℚ]
      K.linearDualCochainComplex.homology n :=
  (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv.symm.toLinearMap.comp
    (K.sc n).linearDual.moduleCatHomologyClass

theorem i1_chainDualCycleClass_surjective : Function.Surjective (i1_chainDualCycleClass K n) :=
  (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv.symm.surjective.comp
    (K.sc n).linearDual.moduleCatHomologyClass_surjective

set_option backward.isDefEq.respectTransparency false in
theorem i1_chainDualCycleClass_pairing
    (φ : LinearMap.ker (K.sc n).f.hom.dualMap) (z : LinearMap.ker (K.sc n).g.hom) :
    K.linearDualHomologyEquiv n (i1_chainDualCycleClass K n φ)
      ((K.sc n).moduleCatHomologyClass z) = (φ.val : Module.Dual ℚ (K.sc n).X₂) z.val := by
  let e := (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv
  change (K.sc n).linearDualHomologyEquiv
    (e (e.symm ((K.sc n).linearDual.moduleCatHomologyClass φ)))
    ((K.sc n).moduleCatHomologyClass z) = _
  rw [e.apply_symm_apply]
  exact ShortComplex.linearDualHomologyEquiv_class_apply_class (K.sc n) φ z

end HodgeLean.Foundations.BundleResolution
