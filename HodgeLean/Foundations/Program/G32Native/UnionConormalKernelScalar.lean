import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealGeneric

/-! # Scalar right inverses for the ambient kernel map -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The identity-ambient scalar extension of inclusion of kernel ideals. -/
def unionKernelMap {R : Type*} [CommRing R] (P I : Ideal R) (hPI : P ≤ I) :
    R ⊗[R] P →ₗ[R] I :=
  (Submodule.inclusion hPI).comp (TensorProduct.lid R P).toLinearMap

/-- Multiplication by an element of the other kernel lifts into the union kernel. -/
def unionKernelScalarLift {R : Type*} [CommRing R]
    (P I J : Ideal R) (hP : P = I ⊓ J) (a : J) :
    I →ₗ[R] R ⊗[R] P :=
  (TensorProduct.lid R P).symm.toLinearMap.comp
    ((LinearEquiv.ofEq (I ⊓ J : Ideal R) P hP.symm).toLinearMap.comp
      (unionIdealMultiply I J a))

/-- The kernel lift is a right inverse up to multiplication by its scalar. -/
lemma unionKernelMap_scalarLift {R : Type*} [CommRing R]
    (P I J : Ideal R) (hP : P = I ⊓ J) (a : J) :
    (unionKernelMap P I (hP.trans_le inf_le_left)).comp
      (unionKernelScalarLift P I J hP a) = a.val • (LinearMap.id : I →ₗ[R] I) := by
  subst P
  ext x
  simp [unionKernelMap, unionKernelScalarLift, unionIdealMultiply]

/-- Scalar extension of the kernel lift retains its scalar right-inverse equation. -/
lemma unionKernelMap_baseChange_scalarLift
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (P I J : Ideal R) (hP : P = I ⊓ J) (a : J) :
    ((unionKernelMap P I (hP.trans_le inf_le_left)).baseChange A).comp
        ((unionKernelScalarLift P I J hP a).baseChange A) =
      algebraMap R A a.val • (LinearMap.id : A ⊗[R] I →ₗ[A] A ⊗[R] I) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b x =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    have hx := LinearMap.congr_fun (unionKernelMap_scalarLift P I J hP a) x
    change unionKernelMap P I (hP.trans_le inf_le_left) (unionKernelScalarLift P I J hP a x) = a.val • x at hx
    change b ⊗ₜ[R] (unionKernelMap P I (hP.trans_le inf_le_left) (unionKernelScalarLift P I J hP a x)) = _
    rw [hx]
    change b ⊗ₜ[R] (a.val • x) = algebraMap R A a.val • (b ⊗ₜ[R] x)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    exact Algebra.smul_def _ _
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

#print axioms unionKernelMap_scalarLift
#print axioms unionKernelMap_baseChange_scalarLift
end HodgeLean.Foundations.Program.G32Native
