import HodgeLean.Foundations.QuotientDuality.ProperCyclePolynomialMatrixEquations

/-! # Actual real coordinates of finite complex matrices -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- Separating real and imaginary matrix entries retains the original finite product topology.
Source: Complex.equivRealProdCLM; Homeomorph.piCongrLeft.
HC no distance; AV milestone no distance. -/
def properCycle_matrix_real_coordinates {ι : Type*} :
    Matrix ι ι ℂ ≃ₜ ((ι × ι) ⊕ (ι × ι) → ℝ) where
  toFun M := Sum.elim (fun ij => (M ij.1 ij.2).re) (fun ij => (M ij.1 ij.2).im)
  invFun x i j := Complex.equivRealProdCLM.symm (x (.inl (i,j)), x (.inr (i,j)))
  left_inv M := by ext i j <;> rfl
  right_inv x := by funext k; cases k <;> rfl
  continuous_toFun := continuous_pi fun k => by
    cases k with
    | inl ij => exact Complex.continuous_re.comp ((continuous_apply ij.2).comp (continuous_apply ij.1))
    | inr ij => exact Complex.continuous_im.comp ((continuous_apply ij.2).comp (continuous_apply ij.1))
  continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
    Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_apply (Sum.inl (i,j) : (ι × ι) ⊕ (ι × ι))).prodMk
        (continuous_apply (Sum.inr (i,j) : (ι × ι) ⊕ (ι × ι))))

/-- Finite complex matrices have actual Euclidean real coordinates.
Source: properCycle_matrix_real_coordinates; EuclideanSpace.equiv.
HC no distance; AV milestone no distance. -/
def properCycle_matrix_euclidean_coordinates {ι : Type*} [Fintype ι] :
    Matrix ι ι ℂ ≃ₜ EuclideanSpace ℝ (Fin (Fintype.card ((ι × ι) ⊕ (ι × ι)))) :=
  properCycle_matrix_real_coordinates.trans
    ((Homeomorph.piCongrLeft (Y := fun _ => ℝ) (Fintype.equivFin _)).trans
      (EuclideanSpace.equiv _ ℝ).symm.toHomeomorph)

/-- Euclidean coordinate evaluation retains each original real and imaginary matrix entry.
Source: Homeomorph.piCongrLeft_apply_apply.
HC no distance; AV milestone no distance. -/
theorem properCycle_matrix_euclidean_coordinates_eval {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (k : (ι × ι) ⊕ (ι × ι)) :
    properCycle_matrix_euclidean_coordinates M (Fintype.equivFin _ k) =
      properCycle_matrix_real_coordinates M k := by
  change (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (Fintype.equivFin _))
    (properCycle_matrix_real_coordinates M) (Fintype.equivFin _ k) = _
  exact Homeomorph.piCongrLeft_apply_apply _ _ _

end HodgeLean.Foundations.QuotientDuality
