import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootCoverMaps

/-! Generation of the coordinate-root tensor algebra by its literal parameter roots. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem coordinate_root_adjoin_eq_top
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (n m : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) :
    let P := MvPolynomial (Fin n) k
    let B := ULift.{0} P
    letI := (rootParameterMap k n m).toRingHom.toAlgebra
    letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
    letI : Module P B := Algebra.toModule (R := P) (A := B)
    letI := c.toRingHom.toAlgebra
    let T := B ⊗[P] R
    Algebra.adjoin R (Set.range (fun j : Fin n =>
      algebraMap B T (ULift.up (MvPolynomial.X j)))) = ⊤ := by
  intro P B
  letI := (rootParameterMap k n m).toRingHom.toAlgebra
  letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
  letI : Module P B := Algebra.toModule (R := P) (A := B)
  letI := c.toRingHom.toAlgebra
  letI : IsScalarTower P P B := IsScalarTower.of_algebraMap_eq' (by
    rw [Algebra.algebraMap_self, RingHom.comp_id])
  letI : SMulCommClass P P B := ⟨fun p q b => by
    change rootParameterMap k n m p * (rootParameterMap k n m q * b) =
      rootParameterMap k n m q * (rootParameterMap k n m p * b)
    exact mul_left_comm _ _ _⟩
  intro T
  letI : SMul B T := (inferInstance : Algebra B T).toSMul
  letI : Module B T := Algebra.toModule (R := B) (A := T)
  letI : IsScalarTower P B T := IsScalarTower.of_algebraMap_eq fun p =>
    (Algebra.TensorProduct.includeLeft.commutes p).symm
  letI : IsScalarTower P R T := IsScalarTower.of_algebraMap_eq fun p =>
    (Algebra.TensorProduct.includeRight.commutes p).symm
  let wT (j : Fin n) : T := algebraMap B T (ULift.up (MvPolynomial.X j))
  let S := Algebra.adjoin R (Set.range wT)
  let wS (j : Fin n) : S := ⟨wT j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  letI : Algebra k S := ((algebraMap R S).comp (algebraMap k R)).toAlgebra
  let fS : R →ₐ[k] S := { algebraMap R S with commutes' := fun _ => rfl }
  have hroot (j : Fin n) : wS j ^ m = fS (c (MvPolynomial.X j)) := by
    apply Subtype.ext
    change algebraMap B T (ULift.up (MvPolynomial.X j)) ^ m =
      algebraMap R T (c (MvPolynomial.X j))
    rw [← map_pow]
    have H : (ULift.up (MvPolynomial.X j) : B) ^ m = algebraMap P B (MvPolynomial.X j) := by
      change _ = rootParameterMap k n m (MvPolynomial.X j)
      rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_X]
      rfl
    rw [H, ← IsScalarTower.algebraMap_apply P B T, IsScalarTower.algebraMap_apply P R T]
    rfl
  obtain ⟨φ, hφR, hφW⟩ := coordinate_root_tensor_lift n m c fS wS hroot
  change T →+* S at φ
  change (∀ r, φ (algebraMap R T r) = fS r) at hφR
  change (∀ j, φ (wT j) = wS j) at hφW
  have hid : S.val.toRingHom.comp φ = RingHom.id T := by
    apply coordinate_root_tensor_ext n m c
    · intro r
      change (φ (algebraMap R T r) : S).val = algebraMap R T r
      rw [hφR]
      rfl
    · intro j
      change (φ (wT j) : S).val = wT j
      rw [hφW]
  apply eq_top_iff.mpr
  intro x hx
  have he : (φ x : S).val = x := RingHom.congr_fun hid x
  exact he ▸ (φ x).property

#print axioms coordinate_root_adjoin_eq_top
end HodgeLean.Foundations.QuotientDuality
