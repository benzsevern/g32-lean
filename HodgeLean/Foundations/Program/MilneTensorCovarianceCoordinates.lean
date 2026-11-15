import HodgeLean.Foundations.Program.MilneTensorFormProjection

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {α β γ δ ι : Type*}

def m1b_sumCoordinateMap (L : (α → ℂ) →ₗ[ℂ] (β → ℂ))
    (N : (γ → ℂ) →ₗ[ℂ] (δ → ℂ)) :
    (α ⊕ γ → ℂ) →ₗ[ℂ] (β ⊕ δ → ℂ) where
  toFun x := Sum.elim (L (fun i => x (Sum.inl i))) (N (fun i => x (Sum.inr i)))
  map_add' x y := by
    funext i
    cases i with
    | inl i => exact congrFun (L.map_add _ _) i
    | inr i => exact congrFun (N.map_add _ _) i
  map_smul' c x := by
    funext i
    cases i with
    | inl i => exact congrFun (L.map_smul c _) i
    | inr i => exact congrFun (N.map_smul c _) i

def m1b_matrixCoordinateEquiv : ((ι × ι) → ℂ) ≃ₗ[ℂ] Matrix ι ι ℂ where
  toFun x i j := x (i, j)
  invFun Q ij := Q ij.1 ij.2
  left_inv x := rfl
  right_inv Q := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def m1b_matrixCongruenceMap [Fintype ι] (M : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Q := M.transpose * Q * M
  map_add' Q R := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Q := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def m1b_repeatedVectorMap [Fintype ι] (r n : ℕ) (M : Matrix ι ι ℂ) :
    (Fin n × (Fin r × ι) → ℂ) →ₗ[ℂ] (Fin n × (Fin r × ι) → ℂ) where
  toFun x tc := (M *ᵥ (fun i => x (tc.1, tc.2.1, i))) tc.2.2
  map_add' x y := by
    funext tc
    exact congrFun (Matrix.mulVec_add M (fun i => x (tc.1, tc.2.1, i))
      (fun i => y (tc.1, tc.2.1, i))) tc.2.2
  map_smul' c x := by
    funext tc
    exact congrFun (Matrix.mulVec_smul M c (fun i => x (tc.1, tc.2.1, i))) tc.2.2

def m1b_formProjectionCoordinates (ε : ℂ) : ((ι × ι) → ℂ) →ₗ[ℂ] ((ι × ι) → ℂ) :=
  m1b_matrixCoordinateEquiv.symm.toLinearMap.comp
    ((m1b_matrixFormProjection ε).comp m1b_matrixCoordinateEquiv.toLinearMap)

def m1b_congruenceCoordinates [Fintype ι] (M : Matrix ι ι ℂ) :
    ((ι × ι) → ℂ) →ₗ[ℂ] ((ι × ι) → ℂ) :=
  m1b_matrixCoordinateEquiv.symm.toLinearMap.comp
    ((m1b_matrixCongruenceMap M).comp m1b_matrixCoordinateEquiv.toLinearMap)

end HodgeLean.Foundations.Program
