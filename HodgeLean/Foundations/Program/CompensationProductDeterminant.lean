import HodgeLean.Foundations.HermitianForm
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Determinants of orthogonal sums of Hermitian forms -/

noncomputable section
set_option maxHeartbeats 400000
open Module HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program

variable {a : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
  {U V Z : Type*} [AddCommGroup U] [Module (QuadraticAlgebra ℚ a 0) U]
  [AddCommGroup V] [Module (QuadraticAlgebra ℚ a 0) V]
  [AddCommGroup Z] [Module (QuadraticAlgebra ℚ a 0) Z]

/-- The rational Gram determinant multiplies under an orthogonal direct sum.
Source: Bourbaki, *Algebra*, Chapter IX, §2; Mathlib `Matrix.det_fromBlocks_zero₂₁`. -/
theorem cp_gramDet_orthogonalSum
    (HU : U →ₗ⋆[QuadraticAlgebra ℚ a 0] U →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0)
    (HV : V →ₗ⋆[QuadraticAlgebra ℚ a 0] V →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0)
    (HZ : Z →ₗ⋆[QuadraticAlgebra ℚ a 0] Z →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0)
    (hU : HU.IsSymm) (hV : HV.IsSymm) (hZ : HZ.IsSymm)
    (e : (U × V) ≃ₗ[QuadraticAlgebra ℚ a 0] Z)
    (h : ∀ x y, HZ (e x) (e y) = HU x.1 y.1 + HV x.2 y.2)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bU : Basis ι (QuadraticAlgebra ℚ a 0) U) (bV : Basis κ (QuadraticAlgebra ℚ a 0) V) :
    gramDetℚ HZ ((bU.prod bV).map e) = gramDetℚ HU bU * gramDetℚ HV bV := by
  have hm : LinearMap.toMatrix₂ ((bU.prod bV).map e) ((bU.prod bV).map e) HZ =
      Matrix.fromBlocks (LinearMap.toMatrix₂ bU bU HU) 0 0 (LinearMap.toMatrix₂ bV bV HV) := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix₂_apply, h]
  apply QuadraticAlgebra.algebraMap_injective (a := a) (b := 0)
  rw [map_mul, algebraMap_gramDetℚ hZ, algebraMap_gramDetℚ hU, algebraMap_gramDetℚ hV]
  change (LinearMap.toMatrix₂ _ _ HZ).det =
    (LinearMap.toMatrix₂ bU bU HU).det * (LinearMap.toMatrix₂ bV bV HV).det
  rw [hm, Matrix.det_fromBlocks_zero₂₁]

/-- The determinant class of an orthogonal sum is the product of determinant classes.
Source: `cp_gramDet_orthogonalSum`, basis independence of `detClass`. -/
theorem cp_detClass_orthogonalSum
    [Module.Finite (QuadraticAlgebra ℚ a 0) U]
    [Module.Finite (QuadraticAlgebra ℚ a 0) V]
    [Module.Finite (QuadraticAlgebra ℚ a 0) Z]
    (HU : U →ₗ⋆[QuadraticAlgebra ℚ a 0] U →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0)
    (HV : V →ₗ⋆[QuadraticAlgebra ℚ a 0] V →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0)
    (HZ : Z →ₗ⋆[QuadraticAlgebra ℚ a 0] Z →ₗ[QuadraticAlgebra ℚ a 0] QuadraticAlgebra ℚ a 0)
    (hU : HU.IsSymm) (hV : HV.IsSymm) (hZ : HZ.IsSymm)
    (hnU : HU.Nondegenerate) (hnV : HV.Nondegenerate) (hnZ : HZ.Nondegenerate)
    (e : (U × V) ≃ₗ[QuadraticAlgebra ℚ a 0] Z)
    (h : ∀ x y, HZ (e x) (e y) = HU x.1 y.1 + HV x.2 y.2) :
    detClass HZ hZ hnZ = detClass HU hU hnU * detClass HV hV hnV := by
  let bU := Module.finBasis (QuadraticAlgebra ℚ a 0) U
  let bV := Module.finBasis (QuadraticAlgebra ℚ a 0) V
  rw [detClass_eq hZ hnZ ((bU.prod bV).map e), detClass_eq hU hnU bU,
    detClass_eq hV hnV bV, ← QuotientGroup.mk_mul]
  congr 1
  ext
  exact cp_gramDet_orthogonalSum HU HV HZ hU hV hZ e h bU bV

end HodgeLean.Foundations.Program
