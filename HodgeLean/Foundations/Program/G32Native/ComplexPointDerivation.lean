import HodgeLean.Foundations.Program.G32Native.AnalyticPointDerivation

/-! # Complex scalar compatibility of point derivatives of original analytic germs -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- A germ map preserving the original complex constants gives the actual
complex scalar tower on values at its point. -/
theorem analyticPoint_scalarTower (d : ℕ)
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (φ : R →+* s2e_nativeAnalyticGermRing d)
    (hC : ∀ c : ℂ, φ (algebraMap ℂ R c) = s2e_nativeAnalytic_constant d c) :
    letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    IsScalarTower ℂ R ℂ := by
  letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change c = s2e_nativeAnalyticGerm_value d (φ (algebraMap ℂ R c))
  rw [hC]
  rfl

/-- Differentiation through a constant-preserving original germ map is a
complex derivation with the same original point derivative values. -/
def analyticComplexPointDerivation (d : ℕ) (v : Fin d → ℂ)
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (φ : R →+* s2e_nativeAnalyticGermRing d)
    (hC : ∀ c : ℂ, φ (algebraMap ℂ R c) = s2e_nativeAnalytic_constant d c) :
    letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    Derivation ℂ R ℂ := by
  letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  letI : IsScalarTower ℂ R ℂ := analyticPoint_scalarTower d φ hC
  let D := analyticPointDerivation d v φ
  refine {
    toFun := D
    map_add' := fun r s => map_add D r s
    map_smul' := ?_
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }
  intro c r
  change D (c • r) = c • D r
  rw [Algebra.smul_def, D.leibniz]
  have hc : D (algebraMap ℂ R c) = 0 := by
    change s2e_nativeAnalyticGerm_value d
      (s2e_nativeAnalytic_derivation d v (φ (algebraMap ℂ R c))) = 0
    rw [hC, s2e_nativeAnalytic_derivation_constant, map_zero]
  rw [hc, smul_zero, add_zero, IsScalarTower.algebraMap_smul]

#print axioms analyticComplexPointDerivation
#print axioms analyticPoint_scalarTower
end HodgeLean.Foundations.Program.G32Native
