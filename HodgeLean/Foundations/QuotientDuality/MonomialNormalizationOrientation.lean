import HodgeLean.Foundations.QuotientDuality.MonomialGaloisRootCover
import HodgeLean.Foundations.QuotientDuality.MonomialRootParameterSmooth
import HodgeLean.Foundations.QuotientDuality.MonomialAffineQuotientOrientation

/-! Coherent local orientations for actual normalizations of etale monomial charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem monomial_normalization_coherent_orientation
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra ℂ R] [Algebra R K] [Algebra ℂ K] [IsScalarTower ℂ R K]
    [Algebra.FiniteType ℂ (integralClosure R K)]
    (n m : ℕ) (hm : 0 < m)
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε * ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤) :
    Nonempty (LocalRationalOrientation
      (TopCat.of (ComplexPoint (Over.mk (affineSpecStructureMap (integralClosure R K)))))
      (2 * n)) := by
  obtain ⟨A, hA, hdom, hnormal, i, b, σ, β, hb, hσ, hβ, hfinite, hβR, hβσ, hparam,
    G, hG, hFin, ρ, hfixed⟩ :=
    monomial_normalization_galois_root_cover ℂ n m hm R K c hc hinj α ε hε v hv hgen
  letI := hA
  letI : IsDomain A := hdom
  letI : IsIntegrallyClosed A := hnormal
  letI : Algebra R A := i.toAlgebra
  letI : Algebra ℂ A := (i.comp (algebraMap ℂ R)).toAlgebra
  letI : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Group G := hG
  letI : Finite G := hFin
  letI : SmoothOfRelativeDimension n (affineSpecStructureMap A) :=
    monomial_root_parameter_spec_smooth ℂ R A n m c b hb hparam
  letI : Smooth (affineSpecStructureMap A) :=
    SmoothOfRelativeDimension.smooth n (affineSpecStructureMap A)
  letI : LocallyOfFiniteType (affineSpecStructureMap A) := inferInstance
  letI : Algebra.FiniteType ℂ A := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.Spec_iff.mp
      (inferInstance : LocallyOfFiniteType (affineSpecStructureMap A)))
  let βC : integralClosure R K →ₐ[ℂ] A := { β with
    commutes' z := by
      change β (algebraMap ℂ (integralClosure R K) z) = i (algebraMap ℂ R z)
      exact (congrArg β (IsScalarTower.algebraMap_apply ℂ R (integralClosure R K) z)).trans
        (RingHom.congr_fun hβR (algebraMap ℂ R z)) }
  let ρC : G →* (A ≃ₐ[ℂ] A) := {
    toFun g := (ρ g).restrictScalars ℂ
    map_one' := by ext a; change ρ 1 a = a; rw [map_one]; rfl
    map_mul' := by intro g h; ext a; change ρ (g * h) a = ρ g (ρ h a); rw [map_mul]; rfl }
  exact affine_invariant_presentation_coherent_orientation n ρC βC hβ hfinite hfixed

#print axioms monomial_normalization_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
