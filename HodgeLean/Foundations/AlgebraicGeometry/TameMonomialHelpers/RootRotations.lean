import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.CoordinateRootCover
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Rotations of universal parameter roots
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- Independent unit scalings of polynomial coordinates form an algebra automorphism.
Source: Mathlib, MvPolynomial.aeval, MvPolynomial.algHom_ext and AlgEquiv.ofAlgHom. -/
def variableScaling
    (k : Type*) [CommRing k] (n : ℕ) (a : Fin n → kˣ) :
    MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.C (a i : k) * MvPolynomial.X i)
    (MvPolynomial.aeval fun i => MvPolynomial.C (↑((a i)⁻¹) : k) * MvPolynomial.X i)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_C,
        AlgHom.id_apply, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← MvPolynomial.C_mul, Units.inv_mul, MvPolynomial.C_1, one_mul])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_C,
        AlgHom.id_apply, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← MvPolynomial.C_mul, Units.mul_inv, MvPolynomial.C_1, one_mul])

example (k : Type*) [CommRing k] (n : ℕ) (a : Fin n → kˣ) (i : Fin n) :
    variableScaling k n a (MvPolynomial.X i) =
      MvPolynomial.C (a i : k) * MvPolynomial.X i := MvPolynomial.aeval_X _ _

/-- Root-of-unity scalings preserve the parameter power map.
Source: Mathlib, MvPolynomial.expand_X and MvPolynomial.algHom_ext. -/
theorem variableScaling_expand
    (k : Type*) [CommRing k] (n m : ℕ) (a : Fin n → kˣ)
    (ha : ∀ i, (a i : k) ^ m = 1) :
    (variableScaling k n a).toAlgHom.comp (MvPolynomial.expand m) =
      MvPolynomial.expand m := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.expand_X, map_pow]
  rw [show (variableScaling k n a).toAlgHom (MvPolynomial.X i) =
    MvPolynomial.C (a i : k) * MvPolynomial.X i from MvPolynomial.aeval_X _ _]
  rw [mul_pow, ← MvPolynomial.C_pow, ha i, MvPolynomial.C_1, one_mul]

/-- Diagonal root rotations act on the lifted root polynomial ring over the original parameter ring.
Source: Mathlib, ULift.algEquiv and variableScaling_expand. -/
theorem rootPolynomial_rotation
    (k : Type*) [CommRing k] (n m : ℕ) (a : Fin n → kˣ)
    (ha : ∀ i, (a i : k) ^ m = 1) :
    ∃ g : ULift.{0} (MvPolynomial (Fin n) k) ≃+*
        ULift.{0} (MvPolynomial (Fin n) k),
      (∀ p, g (rootParameterMap k n m p) =
        rootParameterMap k n m p) ∧
      ∀ i, g (ULift.up (MvPolynomial.X i)) =
        ULift.up (MvPolynomial.C (a i : k) * MvPolynomial.X i) := by
  let e := ULift.algEquiv (R := k) (A := MvPolynomial (Fin n) k)
  let g := e.trans ((variableScaling k n a).trans e.symm)
  refine ⟨g.toRingEquiv, ?_, ?_⟩
  · intro p
    have H := AlgHom.congr_fun (variableScaling_expand k n m a ha) p
    exact congrArg ULift.up H
  · intro i
    exact congrArg ULift.up (show variableScaling k n a (MvPolynomial.X i) =
      MvPolynomial.C (a i : k) * MvPolynomial.X i from MvPolynomial.aeval_X _ _)

/-- A coefficient algebra automorphism acts on its base change over the unchanged right factor.
Source: Mathlib, Algebra.TensorProduct.congr and Algebra.TensorProduct.map_tmul. -/
theorem tensor_rotation
    {P B R : Type*} [CommRing P] [CommRing B] [CommRing R]
    [Algebra P B] [Algebra P R] (g : B ≃ₐ[P] B) :
    ∃ G : B ⊗[P] R ≃ₐ[R] B ⊗[P] R,
      ∀ b, G (algebraMap B (B ⊗[P] R) b) = algebraMap B (B ⊗[P] R) (g b) := by
  let e := Algebra.TensorProduct.congr g (AlgEquiv.refl : R ≃ₐ[P] R)
  let G : B ⊗[P] R ≃ₐ[R] B ⊗[P] R :=
    { e.toRingEquiv with
      commutes' := fun r => by
        change e (1 ⊗ₜ[P] r) = 1 ⊗ₜ[P] r
        simp [e] }
  refine ⟨G, ?_⟩
  intro b
  change e (b ⊗ₜ[P] 1) = g b ⊗ₜ[P] 1
  simp [e]

/-- Root-of-unity coordinate rotations extend through the actual etale coordinate base change.
Source: Mathlib, Algebra.TensorProduct.congr and rootPolynomial_rotation. -/
theorem coordinate_root_rotation
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (n m : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R)
    (a : Fin n → kˣ) (ha : ∀ j, (a j : k) ^ m = 1) :
    let P := MvPolynomial (Fin n) k
    let B := ULift.{0} P
    letI := (rootParameterMap k n m).toRingHom.toAlgebra
    letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
    letI : Module P B := Algebra.toModule (R := P) (A := B)
    letI := c.toRingHom.toAlgebra
    let T := B ⊗[P] R
    ∃ G : T ≃ₐ[R] T, ∀ j,
      G (algebraMap B T (ULift.up (MvPolynomial.X j))) =
        algebraMap R T (c (MvPolynomial.C (a j : k))) *
          algebraMap B T (ULift.up (MvPolynomial.X j)) := by
  intro P B
  letI := (rootParameterMap k n m).toRingHom.toAlgebra
  letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
  letI : Module P B := Algebra.toModule (R := P) (A := B)
  letI := c.toRingHom.toAlgebra
  intro T
  obtain ⟨e, he, heX⟩ := rootPolynomial_rotation k n m a ha
  let eP : B ≃ₐ[P] B := { e with commutes' := he }
  obtain ⟨G, hG⟩ := tensor_rotation (R := R) eP
  refine ⟨G, ?_⟩
  intro j
  rw [hG]
  change algebraMap B T (e (ULift.up (MvPolynomial.X j))) = _
  rw [heX]
  have hC : ULift.up (MvPolynomial.C (a j : k)) =
      algebraMap P B (MvPolynomial.C (a j : k)) := by
    change ULift.up (MvPolynomial.C (a j : k)) =
      ULift.up (MvPolynomial.expand m (MvPolynomial.C (a j : k)))
    rw [MvPolynomial.expand_C]
  change algebraMap B T (ULift.up (MvPolynomial.C (a j : k)) *
    ULift.up (MvPolynomial.X j)) = _
  rw [map_mul, hC, ← IsScalarTower.algebraMap_apply P B T,
    IsScalarTower.algebraMap_apply P R T]
  rfl

end AlgebraicGeometry.TameMonomialCover.Helpers
