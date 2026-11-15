import HodgeLean.Foundations.Program.G32Native.EtaleAnalyticPointDerivation
import HodgeLean.Foundations.Program.G32Native.PointConormalExtension

/-! # Original analytic tangent representatives of smooth-quotient ideal functionals -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- Every point-valued functional on the original ideal of a smooth
quotient is differentiation in an original etale-coordinate tangent direction. -/
theorem etaleAnalyticIdealFunctional_extends (d : ℕ)
    {B : Type*} [CommRing B] [Algebra ℂ B]
    (P : Algebra.Extension ℂ B) [Algebra.FormallySmooth ℂ P.Ring]
    [Algebra.FormallySmooth ℂ B]
    (φ : P.Ring →+* s2e_nativeAnalyticGermRing d)
    (hC : ∀ z : ℂ, φ (algebraMap ℂ P.Ring z) = s2e_nativeAnalytic_constant d z)
    (c : MvPolynomial (Fin d) ℂ →ₐ[ℂ] P.Ring) (hc : c.toRingHom.Etale)
    (a : Fin d → ℂ)
    (hcoord : ∀ i, φ (c (MvPolynomial.X i)) =
      s2e_nativeAnalytic_constant d (a i) + s2e_nativeAnalytic_coordinate d i)
    (ε : B →ₐ[ℂ] ℂ)
    (hε : ∀ r, ε (algebraMap P.Ring B r) = s2e_nativeAnalyticGerm_value d (φ r)) :
    letI : Algebra P.Ring ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    ∀ f : P.ker →ₗ[P.Ring] ℂ, ∃ v : Fin d → ℂ,
      ∀ r : P.ker, analyticPointDerivation d v φ r.val = f r := by
  letI : Algebra P.Ring ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  letI : Algebra B ℂ := ε.toRingHom.toAlgebra
  letI : IsScalarTower ℂ P.Ring ℂ := analyticPoint_scalarTower d φ hC
  letI : IsScalarTower ℂ B ℂ := IsScalarTower.of_algebraMap_eq (fun z => (ε.commutes z).symm)
  letI : IsScalarTower P.Ring B ℂ := IsScalarTower.of_algebraMap_eq (fun r => (hε r).symm)
  intro f
  obtain ⟨D, hD⟩ := pointIdealFunctional_extends P f
  let E := etaleCoordinateDerivationEquiv ℂ P.Ring d c hc
  let v := E.symm D
  have h : analyticComplexPointDerivation d v φ hC = D :=
    (etaleAnalyticPointDerivation_eq d φ hC c hc a hcoord v).trans (E.apply_symm_apply D)
  refine ⟨v, ?_⟩
  intro r
  exact (DFunLike.congr_fun h r.val).trans (hD r)

#print axioms etaleAnalyticIdealFunctional_extends
end HodgeLean.Foundations.Program.G32Native
