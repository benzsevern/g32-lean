import HodgeLean.Foundations.QuotientDuality.MonomialIntegralComponent
import HodgeLean.Foundations.QuotientDuality.MonomialComponentFiniteType
import HodgeLean.Foundations.QuotientDuality.MonomialFiniteNormalCover
import HodgeLean.Foundations.QuotientDuality.MonomialNormalRootInvariants
import HodgeLean.Foundations.QuotientDuality.MonomialGaloisInvariants
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! A finite Galois invariant presentation of the monomial normalization. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.TameMonomialCover.Helpers
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality
universe w u v

theorem monomial_normalization_galois_root_cover
    (k : Type w) [Field k] [IsAlgClosed k] [CharZero k]
    (n m : ℕ) (hm : 0 < m) (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε * ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤) :
    ∃ (A : Type (max u w)) (hA : CommRing A), letI := hA
      ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A)
        (i : R →+* A) (b : ULift.{0} (MvPolynomial (Fin n) k) →+* A)
        (σ : A →+* AlgebraicClosure K) (β : integralClosure R K →+* A),
        b.Etale ∧ Function.Injective σ ∧ Function.Injective β ∧ β.Finite ∧
        β.comp (algebraMap R (integralClosure R K)) = i ∧
        (∀ z : integralClosure R K, σ (β z) = algebraMap K (AlgebraicClosure K) (z : K)) ∧
        b.comp (rootParameterMap k n m).toRingHom = i.comp c.toRingHom ∧
        (letI : Algebra R A := i.toAlgebra
         ∃ (G : Type (max u w)) (_ : Group G) (_ : Finite G),
           ∃ ρ : G →* (A ≃ₐ[R] A),
             ∀ a : A, (∃ z, β z = a) ↔ ∀ g, ρ g a = a) := by
  let L := AlgebraicClosure K
  let f : K →ₐ[R] L := IsScalarTower.toAlgHom R K L
  let fR : R →ₐ[k] L := IsScalarTower.toAlgHom k R L
  have hinjL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp hinj
  have hcI := etale_parameter_injective n c hc
  have hz (j : Fin n) : algebraMap R L (c (MvPolynomial.X j)) ≠ 0 := by
    intro H
    apply MvPolynomial.X_ne_zero (R := k) j
    apply hcI
    apply hinjL
    rw [H, map_zero, map_zero]
  have hvL : algebraMap K L v ^ m = algebraMap R L ε *
      ∏ j, (algebraMap R L (c (MvPolynomial.X j))) ^ α j := by
    simpa only [map_pow, map_mul, map_prod, ← IsScalarTower.algebraMap_apply R K L]
      using congrArg (algebraMap K L) hv
  obtain ⟨w, u, hw, hu, hmon, hwint, huint⟩ := monomial_root_choices
    n m hm (fun j => c (MvPolynomial.X j)) hz α ε (algebraMap K L v) hvL
  obtain ⟨A, hA, hdom, hnormal, i, b, W, U, σ, hi, hb, hσ, hσi, hσW, hσU,
    hparam, hWpow, hUpow, hUunit, hgenA⟩ :=
    monomial_integral_root_component k n m hm R L c hc fR hinjL ε hε w hw u hu
  letI := hA
  letI : IsDomain A := hdom
  letI : IsIntegrallyClosed A := hnormal
  letI : Algebra R A := i.toAlgebra
  letI : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hi
  letI : Algebra.FiniteType R A :=
    RingHom.finiteType_algebraMap.mp (root_component_finiteType_over_chart k R A n m c i b hb hparam)
  let σA : A →ₐ[R] L := { σ with commutes' := RingHom.congr_fun hσi }
  let V : A := U * ∏ j, W j ^ α j
  have hV : σA V = f v := by
    change σ (U * ∏ j, W j ^ α j) = algebraMap K L v
    rw [map_mul, map_prod, hσU]
    simp_rw [map_pow, hσW]
    exact hmon.symm
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : NeZero (m : k) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k m
  obtain ⟨β, hβ, hβfinite, hβσ, G, hG, hFin, ρ, hfixed⟩ :=
    normal_root_cover_invariant_presentation n m hm
      (algebraMap k K ζ) (hζ.map_of_injective (algebraMap k K).injective)
      v hgen f σA hσ V hV W U hgenA (fun j => c (MvPolynomial.X j)) ε hWpow hUpow
  exact ⟨A, inferInstance, inferInstance, inferInstance, i, b, σ, β.toRingHom,
    hb, hσ, hβ, hβfinite, β.comp_algebraMap, hβσ, hparam, G, hG, hFin, ρ, hfixed⟩

#print axioms monomial_normalization_galois_root_cover
end HodgeLean.Foundations.QuotientDuality
