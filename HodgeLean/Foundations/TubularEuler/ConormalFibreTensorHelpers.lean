import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Tensor fibres of the ideal and its conormal quotient

A scalar map annihilating the ideal makes the two tensor fibres canonically equivalent.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

def conormalFibreTensorToIdeal (I : Ideal R)
    (hI : ∀ r ∈ I, algebraMap R C r = 0) : C ⊗[R] I.Cotangent →ₗ[C] C ⊗[R] I := by
  let f : I →ₗ[R] C ⊗[R] I := TensorProduct.mk R C I 1
  have hkill : ∀ x y : I, f (x * y) = 0 := by
    intro x y
    change (1 : C) ⊗ₜ[R] (x * y) = 0
    have he : x * y = (x : R) • y := Subtype.ext rfl
    rw [he, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, hI x.val x.property,
      zero_mul, TensorProduct.zero_tmul]
  exact (Ideal.Cotangent.lift f hkill).liftBaseChange C

theorem conormalFibreTensorToIdeal_tmul (I : Ideal R)
    (hI : ∀ r ∈ I, algebraMap R C r = 0) (c : C) (u : I) :
    conormalFibreTensorToIdeal I hI (c ⊗ₜ[R] I.toCotangent u) = c ⊗ₜ[R] u := by
  change c • ((1 : C) ⊗ₜ[R] u) = c ⊗ₜ[R] u
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

def conormalFibreTensorFromIdeal (I : Ideal R) : C ⊗[R] I →ₗ[C] C ⊗[R] I.Cotangent :=
  TensorProduct.AlgebraTensorModule.lTensor C C I.toCotangent

theorem conormalFibreTensorFromIdeal_tmul (I : Ideal R) (c : C) (u : I) :
    conormalFibreTensorFromIdeal I (c ⊗ₜ[R] u) = c ⊗ₜ[R] I.toCotangent u := by
  rfl

theorem conormalFibreTensor_inverse (I : Ideal R)
    (hI : ∀ r ∈ I, algebraMap R C r = 0) :
    Function.LeftInverse (conormalFibreTensorToIdeal I hI) (conormalFibreTensorFromIdeal I) ∧
      Function.RightInverse (conormalFibreTensorToIdeal I hI) (conormalFibreTensorFromIdeal I) := by
  constructor
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c u => rw [conormalFibreTensorFromIdeal_tmul, conormalFibreTensorToIdeal_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c u =>
      obtain ⟨u, rfl⟩ := I.toCotangent_surjective u
      rw [conormalFibreTensorToIdeal_tmul, conormalFibreTensorFromIdeal_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]

def conormalFibreTensorEquiv (I : Ideal R)
    (hI : ∀ r ∈ I, algebraMap R C r = 0) : C ⊗[R] I ≃ₗ[C] C ⊗[R] I.Cotangent := {
  __ := conormalFibreTensorFromIdeal I
  invFun := conormalFibreTensorToIdeal I hI
  left_inv := (conormalFibreTensor_inverse I hI).1
  right_inv := (conormalFibreTensor_inverse I hI).2 }

theorem conormalFibreTensorEquiv_tmul (I : Ideal R)
    (hI : ∀ r ∈ I, algebraMap R C r = 0) (c : C) (u : I) :
    conormalFibreTensorEquiv I hI (c ⊗ₜ[R] u) = c ⊗ₜ[R] I.toCotangent u := by
  rfl

#print axioms conormalFibreTensorEquiv_tmul

#print axioms conormalFibreTensor_inverse

#print axioms conormalFibreTensorFromIdeal_tmul

#print axioms conormalFibreTensorToIdeal_tmul

end HodgeLean.Foundations.TubularEuler
