import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Scalar extension commutes with a finite ordered tensor power.
Source: Bourbaki, Algebra, Chapter II, §3, extension of scalars for tensor products. -/
def s4_tensorBaseChangeEquiv {K L V I : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    {B : Type*} (b : Module.Basis B K V) :
    (L ⊗[K] (⨂[K] i : I, V)) ≃ₗ[L] (⨂[L] i : I, L ⊗[K] V) :=
  ((Basis.piTensorProduct (fun _ : I => b)).baseChange L).equiv
    (Basis.piTensorProduct (fun _ : I => b.baseChange L)) (Equiv.refl _)

/-- The tensor scalar-extension equivalence has the specified values on basis tensors. -/
theorem s4_tensorBaseChangeEquiv_basis {K L V I B : Type*}
    [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I] (b : Module.Basis B K V) (v : I → B) :
    s4_tensorBaseChangeEquiv (L := L) (I := I) b
      ((1 : L) ⊗ₜ[K] PiTensorProduct.tprod K (fun i => b (v i))) =
      PiTensorProduct.tprod L (fun i => (1 : L) ⊗ₜ[K] b (v i)) := by
  have he := Module.Basis.equiv_apply
    ((Basis.piTensorProduct (fun _ : I => b)).baseChange L) v
    (Basis.piTensorProduct (fun _ : I => b.baseChange L)) (Equiv.refl _)
  simpa only [s4_tensorBaseChangeEquiv, Module.Basis.baseChange_apply,
    Basis.piTensorProduct_apply, Equiv.refl_apply] using he

/-- On arbitrary rational factors the tensor scalar-extension equivalence is coordinatewise. -/
theorem s4_tensorBaseChangeEquiv_tprod {K L V I B : Type*}
    [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I] (b : Module.Basis B K V) (v : I → V) :
    s4_tensorBaseChangeEquiv (L := L) (I := I) b
      ((1 : L) ⊗ₜ[K] PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod L (fun i => (1 : L) ⊗ₜ[K] v i) := by
  let F : MultilinearMap K (fun _ : I => V) (⨂[L] i : I, L ⊗[K] V) :=
    ((s4_tensorBaseChangeEquiv (L := L) (I := I) b).toLinearMap.restrictScalars K).compMultilinearMap
      ((TensorProduct.mk K L (⨂[K] i : I, V) 1).compMultilinearMap (PiTensorProduct.tprod K))
  let G : MultilinearMap K (fun _ : I => V) (⨂[L] i : I, L ⊗[K] V) :=
    ((PiTensorProduct.tprod L).restrictScalars K).compLinearMap
      (fun _ => TensorProduct.mk K L V 1)
  have h : F = G := by
    apply Module.Basis.ext_multilinear (fun _ : I => b)
    intro v
    exact s4_tensorBaseChangeEquiv_basis b v
  exact congrFun (congrArg DFunLike.coe h) v

end HodgeLean.Foundations.Program
