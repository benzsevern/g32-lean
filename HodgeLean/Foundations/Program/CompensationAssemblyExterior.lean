import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Mathlib.LinearAlgebra.ExteriorPower.Basic

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable (R V T : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup T] [Module R T]

def cq_exteriorDegree (n : ℕ) : ExteriorAlgebra R V →ₗ[R] ⋀[R]^n V :=
  (DFinsupp.lapply n).comp
    (DirectSum.decomposeLinearEquiv (fun k : ℕ => ⋀[R]^k V)).toLinearMap

theorem cq_exteriorDegree_same (n : ℕ) (a : ⋀[R]^n V) :
    cq_exteriorDegree R V n a = a := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k V) (a : ExteriorAlgebra R V)) n = a
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]

theorem cq_exteriorDegree_ne (n k : ℕ) (h : k ≠ n) (a : ⋀[R]^k V) :
    cq_exteriorDegree R V n a = 0 := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k V) (a : ExteriorAlgebra R V)) n = 0
  rw [DirectSum.decompose_coe, DirectSum.of_eq_of_ne _ _ _ h.symm]

def cq_exteriorTensorComponent (i j : ℕ) :
    ExteriorAlgebra R (V × T) →ₗ[R] (⋀[R]^i V) ⊗[R] (⋀[R]^j T) :=
  TensorProduct.map (cq_exteriorDegree R V i) (cq_exteriorDegree R T j) ∘ₗ
    (GradedTensorProduct.of R (fun k : ℕ => ⋀[R]^k V)
      (fun k : ℕ => ⋀[R]^k T)).symm.toLinearMap ∘ₗ
        (ExteriorAlgebra.prodEquivTensor R V T).toLinearEquiv.toLinearMap

theorem cq_exteriorTensorComponent_same (i j : ℕ) (a : ⋀[R]^i V) (b : ⋀[R]^j T) :
    cq_exteriorTensorComponent R V T i j
      (ExteriorAlgebra.map (LinearMap.inl R V T) a *
        ExteriorAlgebra.map (LinearMap.inr R V T) b) = a ⊗ₜ[R] b := by
  change TensorProduct.map (cq_exteriorDegree R V i) (cq_exteriorDegree R T j)
    ((GradedTensorProduct.of R (fun k : ℕ => ⋀[R]^k V)
      (fun k : ℕ => ⋀[R]^k T)).symm
        (ExteriorAlgebra.prodEquivTensor R V T
          (ExteriorAlgebra.map (LinearMap.inl R V T) a *
            ExteriorAlgebra.map (LinearMap.inr R V T) b))) = _
  rw [← ExteriorAlgebra.prodEquivTensor_symm_tmul R V T,
    AlgEquiv.apply_symm_apply]
  change TensorProduct.map (cq_exteriorDegree R V i) (cq_exteriorDegree R T j)
    ((a : ExteriorAlgebra R V) ⊗ₜ[R] (b : ExteriorAlgebra R T)) = _
  rw [TensorProduct.map_tmul, cq_exteriorDegree_same, cq_exteriorDegree_same]

theorem cq_exteriorTensorComponent_ne (i j k l : ℕ) (h : l ≠ j)
    (a : ⋀[R]^k V) (b : ⋀[R]^l T) :
    cq_exteriorTensorComponent R V T i j
      (ExteriorAlgebra.map (LinearMap.inl R V T) a *
        ExteriorAlgebra.map (LinearMap.inr R V T) b) = 0 := by
  change TensorProduct.map (cq_exteriorDegree R V i) (cq_exteriorDegree R T j)
    ((GradedTensorProduct.of R (fun k : ℕ => ⋀[R]^k V)
      (fun k : ℕ => ⋀[R]^k T)).symm
        (ExteriorAlgebra.prodEquivTensor R V T
          (ExteriorAlgebra.map (LinearMap.inl R V T) a *
            ExteriorAlgebra.map (LinearMap.inr R V T) b))) = _
  rw [← ExteriorAlgebra.prodEquivTensor_symm_tmul R V T,
    AlgEquiv.apply_symm_apply]
  change TensorProduct.map (cq_exteriorDegree R V i) (cq_exteriorDegree R T j)
    ((a : ExteriorAlgebra R V) ⊗ₜ[R] (b : ExteriorAlgebra R T)) = _
  rw [TensorProduct.map_tmul, cq_exteriorDegree_ne R T j l h, TensorProduct.tmul_zero]

end HodgeLean.Foundations.Program
