import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.UnitRootCover
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootChoices
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootRotations
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.UnitRootRotations
import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootCoverMaps
import Mathlib.RingTheory.RingHom.Integral

/-! # Universal integral covers for all monomial roots
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace AlgebraicGeometry.TameMonomialCover.Helpers
universe w
variable {κbase : Type w} [Field κbase] [IsAlgClosed κbase] [CharZero κbase]
universe u v

/-- The universal coordinate-root and unit-root constructions give an integral cover etale over the root polynomial ring, with its prescribed ambient-field map.
Source: Mathlib, Algebra.Etale.baseChange, StandardEtalePair and Algebra.IsPushout.isIntegral. -/
theorem universal_root_cover
    (n m : ℕ) (hm : 0 < m) (R : Type u) (L : Type v)
    [CommRing R] [Field L] [Algebra κbase R] [Algebra κbase L]
    (c : MvPolynomial (Fin n) κbase →ₐ[κbase] R) (hc : c.toRingHom.Etale)
    (f : R →ₐ[κbase] L) (ε : R) (hε : IsUnit ε)
    (w : Fin n → L) (hw : ∀ j, w j ^ m = f (c (MvPolynomial.X j)))
    (u : L) (hu : u ^ m = f ε) :
    ∃ (A : Type (max u w)) (hA : CommRing A),
      letI := hA
      ∃ (i : R →+* A) (b : ULift.{0} (MvPolynomial (Fin n) κbase) →+* A)
        (W : Fin n → A) (U : A) (τ : A →+* L),
        i.IsIntegral ∧ b.Etale ∧
        b.comp (rootParameterMap κbase n m).toRingHom = i.comp c.toRingHom ∧
        (∀ j, W j ^ m = i (c (MvPolynomial.X j))) ∧ U ^ m = i ε ∧ IsUnit U ∧
        (∀ r, τ (i r) = f r) ∧ (∀ j, τ (W j) = w j) ∧ τ U = u ∧
        (∀ j, W j = b (ULift.up (MvPolynomial.X j))) ∧
        (∀ a : Fin n → κbaseˣ, (∀ j, (a j : κbase) ^ m = 1) →
          ∃ G : A ≃+* A, (∀ r, G (i r) = i r) ∧
            (∀ j, G (W j) = i (c (MvPolynomial.C (a j : κbase))) * W j) ∧ G U = U) ∧
        (∀ F H : A →+* κbase, (∀ r, F (i r) = H (i r)) →
          (∀ j, F (W j) = H (W j)) → F U = H U → F = H) := by
  let P := MvPolynomial (Fin n) κbase
  let B := ULift.{0} P
  letI := (rootParameterMap κbase n m).toRingHom.toAlgebra
  letI : SMul P B := (rootParameterMap κbase n m).toRingHom.toAlgebra.toSMul
  letI : Module P B := Algebra.toModule (R := P) (A := B)
  letI := c.toRingHom.toAlgebra
  let T := B ⊗[P] R
  letI : SMul B T := (inferInstance : Algebra B T).toSMul
  letI : Module B T := Algebra.toModule (R := B) (A := T)
  obtain ⟨wT, hwT, hEt, hInt, hwTcan⟩ := coordinate_root_tensor n m hm c hc
  letI : Algebra.Etale B T := hEt
  letI : Algebra.IsIntegral R T := hInt
  obtain ⟨τT, hτTR, hτTw⟩ := coordinate_root_tensor_lift n m c f w hw
  have hmC : (m : κbase) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmB : IsUnit (m : B) := by
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hmC).map (algebraMap κbase B)
  have hmT : IsUnit (m : T) := by
    simpa only [map_natCast] using hmB.map (algebraMap B T)
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hmT
  let Q := unitRootPair T m hm (algebraMap R T ε) a ha
  let A := Q.Ring
  let i : R →+* A := (algebraMap T A).comp (algebraMap R T)
  let b : B →+* A := (algebraMap T A).comp (algebraMap B T)
  let W (j : Fin n) : A := algebraMap T A (wT j)
  let U : A := Q.X
  have hεT : IsUnit (algebraMap R T ε) := hε.map (algebraMap R T)
  have hIntQ : (algebraMap T A).IsIntegral := algebraMap_isIntegral_iff.mpr
    (unitRootPair_integral T m hm (algebraMap R T ε) a ha hεT)
  have hEtQ : (algebraMap T A).Etale := (RingHom.etale_algebraMap).mpr inferInstance
  have huunit : IsUnit u := (isUnit_pow_iff hm.ne').mp (by rw [hu]; exact hε.map f)
  have huT : u ^ m = τT (algebraMap R T ε) := hu.trans (hτTR ε).symm
  obtain ⟨τ, hτT, hτU⟩ := unitRootPair_lift m hm (algebraMap R T ε) a ha τT u huT huunit
  refine ⟨A, inferInstance, i, b, W, U, τ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hτU, ?_, ?_, ?_⟩
  · exact (algebraMap_isIntegral_iff.mpr hInt).trans _ _ hIntQ
  · letI : Algebra B A := b.toAlgebra
    letI : SMul B A := (inferInstance : Algebra B A).toSMul
    letI : Module B A := Algebra.toModule (R := B) (A := A)
    haveI : IsScalarTower B T A := IsScalarTower.of_algebraMap_eq' (R := B) (S := T) (A := A) rfl
    letI : Algebra.Etale B A := Algebra.Etale.comp B T A
    change (algebraMap B A).Etale
    exact (RingHom.etale_algebraMap).mpr inferInstance
  · apply RingHom.ext
    intro p
    change algebraMap T A (algebraMap B T (algebraMap P B p)) =
      algebraMap T A (algebraMap R T (c p))
    rw [← IsScalarTower.algebraMap_apply P B T, IsScalarTower.algebraMap_apply P R T]
    rfl
  · intro j
    change algebraMap T A (wT j) ^ m = _
    rw [← map_pow, hwT]
    rfl
  · change Q.X ^ m = algebraMap T Q.Ring (algebraMap R T ε)
    have H := Q.hasMap_X.1
    change Polynomial.aeval Q.X (Polynomial.X ^ m - Polynomial.C (algebraMap R T ε)) = 0 at H
    simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using H
  · have H := Q.hasMap_X.2
    change IsUnit (Polynomial.aeval Q.X Polynomial.X) at H
    simpa only [Polynomial.aeval_X] using H
  · intro r
    exact (hτT (algebraMap R T r)).trans (hτTR r)
  · intro j
    change τ (algebraMap T A (wT j)) = w j
    rw [hτT, hwTcan]
    exact hτTw j
  · intro j
    change algebraMap T A (wT j) = algebraMap T A (algebraMap B T (ULift.up (MvPolynomial.X j)))
    rw [hwTcan]

  · intro weights haRoot
    obtain ⟨g, hg⟩ := coordinate_root_rotation n m c weights haRoot
    obtain ⟨G, hG, hGU⟩ := unitRoot_rotation T m hm (algebraMap R T ε) a ha
      g.toRingEquiv (g.commutes ε)
    refine ⟨G, ?_, ?_, hGU⟩
    · intro r
      change G (algebraMap T A (algebraMap R T r)) = algebraMap T A (algebraMap R T r)
      rw [hG]
      exact congrArg (algebraMap T A) (g.commutes r)
    · intro j
      change G (algebraMap T A (wT j)) =
        algebraMap T A (algebraMap R T (c (MvPolynomial.C (weights j : κbase)))) * algebraMap T A (wT j)
      rw [hG, hwTcan]
      change algebraMap T A (g (algebraMap B T (ULift.up (MvPolynomial.X j)))) = _
      rw [hg, map_mul]
  · intro F H hR hW hU
    apply standardEtale_ringHom_ext Q F H
    · have heq : F.comp (algebraMap T A) = H.comp (algebraMap T A) := by
        apply coordinate_root_tensor_ext n m c
        · exact hR
        · intro j
          have Hroot := hW j
          change F (algebraMap T A (wT j)) = H (algebraMap T A (wT j)) at Hroot
          rw [hwTcan] at Hroot
          exact Hroot
      exact heq
    · exact hU

end AlgebraicGeometry.TameMonomialCover.Helpers
