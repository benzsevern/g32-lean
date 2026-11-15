import HodgeLean.Foundations.Program.G32Native.AnalyticModulePointFunctional

/-! # Linear ambient-direction maps into actual analytic point fibres -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original equation derivative functional depends complex linearly on
the original ambient direction. -/
def analyticModulePointDerivativeMap (d : ℕ)
    {R : Type*} [CommRing R] (φ : R →+* s2e_nativeAnalyticGermRing d)
    {N : Type*} [AddCommGroup N] [Module R N] (j : N →ₗ[R] R)
    (hj : ∀ n, s2e_nativeAnalyticGerm_value d (φ (j n)) = 0) :
    letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    (Fin d → ℂ) →ₗ[ℂ] (N →ₗ[R] ℂ) := by
  letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  refine {
    toFun := fun v => analyticModulePointDerivative d v φ j hj
    map_add' := ?_
    map_smul' := ?_ }
  · intro v w
    ext n
    exact analyticPointDerivation_add_direction d v w φ (j n)
  · intro c v
    ext n
    exact analyticPointDerivation_smul_direction d c v φ (j n)

/-- Original ambient directions act complex linearly on the actual affine
point fibre through the canonical affine dual comparison. -/
def affineAnalyticModuleFunctionalMap (d : ℕ)
    (R : CommRingCat.{0}) (φ : R →+* s2e_nativeAnalyticGermRing d)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (j : (moduleSpecΓFunctor (R := R)).obj M →ₗ[R] R)
    (hj : ∀ m, s2e_nativeAnalyticGerm_value d (φ (j m)) = 0) :
    let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
    (Fin d → ℂ) →ₗ[ℂ] Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ε)).obj M)) := by
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := ε.hom.toAlgebra
  exact (affinePointDualEquiv R ε M).symm.toLinearMap.comp
    (analyticModulePointDerivativeMap d φ j hj)

/-- The linear map retains the original fibre functional for each direction. -/
theorem affineAnalyticModuleFunctionalMap_apply (d : ℕ) (v : Fin d → ℂ)
    (R : CommRingCat.{0}) (φ : R →+* s2e_nativeAnalyticGermRing d)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (j : (moduleSpecΓFunctor (R := R)).obj M →ₗ[R] R)
    (hj : ∀ m, s2e_nativeAnalyticGerm_value d (φ (j m)) = 0) :
    affineAnalyticModuleFunctionalMap d R φ M j hj v =
      affineAnalyticModuleFunctional d v R φ M j hj := rfl

#print axioms analyticModulePointDerivativeMap
#print axioms affineAnalyticModuleFunctionalMap
#print axioms affineAnalyticModuleFunctionalMap_apply
end HodgeLean.Foundations.Program.G32Native
