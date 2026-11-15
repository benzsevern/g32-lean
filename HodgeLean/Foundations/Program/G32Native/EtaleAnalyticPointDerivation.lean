import HodgeLean.Foundations.Program.G32Native.ComplexPointDerivation
import HodgeLean.Foundations.Program.G32Native.EtaleCoordinateDerivations

/-! # Analytic point derivations in specified original etale coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- A constant-preserving germ map with the specified original coordinate
germs has exactly the point derivation prescribed by their tangent values. -/
theorem etaleAnalyticPointDerivation_eq (d : ℕ)
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (φ : R →+* s2e_nativeAnalyticGermRing d)
    (hC : ∀ z : ℂ, φ (algebraMap ℂ R z) = s2e_nativeAnalytic_constant d z)
    (c : MvPolynomial (Fin d) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (a : Fin d → ℂ)
    (hcoord : ∀ i, φ (c (MvPolynomial.X i)) =
      s2e_nativeAnalytic_constant d (a i) + s2e_nativeAnalytic_coordinate d i)
    (v : Fin d → ℂ) :
    letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    letI : IsScalarTower ℂ R ℂ := analyticPoint_scalarTower d φ hC
    analyticComplexPointDerivation d v φ hC = etaleCoordinateDerivationEquiv ℂ R d c hc v := by
  letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  letI : IsScalarTower ℂ R ℂ := analyticPoint_scalarTower d φ hC
  apply etaleCoordinateDerivation_ext ℂ R d c hc
  intro i
  rw [etaleCoordinateDerivationEquiv_apply]
  change s2e_nativeAnalyticGerm_value d
    (s2e_nativeAnalytic_derivation d v (φ (c (MvPolynomial.X i)))) = v i
  rw [hcoord, map_add, s2e_nativeAnalytic_derivation_constant,
    s2e_nativeAnalytic_derivation_coordinate, zero_add]
  rfl

#print axioms etaleAnalyticPointDerivation_eq
end HodgeLean.Foundations.Program.G32Native
