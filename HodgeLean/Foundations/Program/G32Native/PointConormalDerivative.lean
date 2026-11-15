import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Point-valued derivations on the ideal cotangent module -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

variable {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R]
  [AddCommGroup M] [Module R M] [Module A M]
  [IsScalarTower A R M] [SMulCommClass A R M]

/-- A point-valued derivation factors through I/I² when the ideal acts by zero
on its value module. The factor retains the value of the original derivation. -/
def pointConormalDerivative (I : Ideal R)
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (d : Derivation A R M) :
    I.Cotangent →ₗ[A] M :=
  Ideal.Cotangent.lift (d.toLinearMap.comp (I.subtype.restrictScalars A)) (by
    intro x y
    change d ((x : R) * (y : R)) = 0
    rw [d.leibniz, hI x x.property, hI y y.property, add_zero])

/-- On the original ideal, a point-valued derivation is linear over the
ambient ring because the ideal acts by zero on its value module. -/
def pointIdealDerivative (I : Ideal R)
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (d : Derivation A R M) : I →ₗ[R] M where
  toFun s := d s
  map_add' s t := by simp only [Submodule.coe_add, map_add]
  map_smul' r s := by
    change d (r * (s : R)) = r • d s
    rw [d.leibniz, hI s s.property, add_zero]

/-- Scalar extension of the ideal derivative evaluates a scalar times an
original ideal class as that scalar times the original derivative. -/
theorem pointIdealDerivative_baseChange_tmul
    {K : Type*} [CommRing K] [Algebra R K] [Module K M] [IsScalarTower R K M]
    (I : Ideal R) (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (d : Derivation A R M)
    (c : K) (s : I) :
    (pointIdealDerivative I hI d).liftBaseChange K (c ⊗ₜ[R] s) = c • d s := rfl

#print axioms pointIdealDerivative
#print axioms pointIdealDerivative_baseChange_tmul
/-- Evaluation on the actual ideal class has exactly the original derivative value. -/
theorem pointConormalDerivative_toCotangent (I : Ideal R)
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (d : Derivation A R M) (s : I) :
    pointConormalDerivative I hI d (I.toCotangent s) = d s := rfl

/-- The factor on the conormal module is uniquely determined by the original
values on ideal sections. -/
theorem pointConormalDerivative_unique (I : Ideal R)
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (d : Derivation A R M)
    (f : I.Cotangent →ₗ[A] M) (hf : ∀ s : I, f (I.toCotangent s) = d s) :
    f = pointConormalDerivative I hI d := by
  ext s
  obtain ⟨s, rfl⟩ := I.toCotangent_surjective s
  exact hf s

/-- The conormal construction is linear in the point-valued derivation. -/
def pointConormalDerivativeMap (I : Ideal R)
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) :
    Derivation A R M →ₗ[A] (I.Cotangent →ₗ[A] M) where
  toFun := pointConormalDerivative I hI
  map_add' d e := by
    ext s
    obtain ⟨s, rfl⟩ := I.toCotangent_surjective s
    rfl
  map_smul' c d := by
    ext s
    obtain ⟨s, rfl⟩ := I.toCotangent_surjective s
    rfl

/-- Zero action on an ideal follows from inclusion in the point's scalar kernel. -/
theorem ideal_scalar_action_zero {K : Type*} [Field K] [Algebra R K]
    (I : Ideal R) (hI : I ≤ RingHom.ker (algebraMap R K)) :
    ∀ r ∈ I, ∀ m : K, r • m = 0 := by
  intro r hr m
  rw [Algebra.smul_def, show algebraMap R K r = 0 from hI hr, zero_mul]

#print axioms pointConormalDerivative
#print axioms pointConormalDerivative_toCotangent
#print axioms pointConormalDerivative_unique
#print axioms pointConormalDerivativeMap
#print axioms ideal_scalar_action_zero
end HodgeLean.Foundations.Program.G32Native
