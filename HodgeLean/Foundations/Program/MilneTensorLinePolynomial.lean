import HodgeLean.Foundations.Program.MilneTensorDiagonal

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]

theorem m1b_orthogonal_line_orbit_polynomial {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (1 : Matrix ι ι ℂ).toBilin', ∀ v,
      f (fun j => m1b_copies r u (v j)) = f v) :
    ∃ p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ M : Matrix ι ι ℂ, ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim
          (fun ij => (M⁻¹.transpose * (1 : Matrix ι ι ℂ) * M⁻¹) ij.1 ij.2)
          (fun tc : Fin n × (Fin r × ι) => v tc.1 tc.2.1 tc.2.2)) p = f (fun j c => M⁻¹ *ᵥ v j c) := by
  obtain ⟨P, hP⟩ := m1b_orthogonal_diagonal_polynomial f hf
  refine ⟨MvPolynomial.rename (Sum.map (fun i => (i, i)) id) P, ?_⟩
  intro M v
  have hdiag (i : ι) : (M⁻¹.transpose * (1 : Matrix ι ι ℂ) * M⁻¹) i i =
      (M⁻¹ i i) ^ 2 := by
    rw [Matrix.mul_one]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_unique]
    rw [show (default : ι) = i from Subsingleton.elim _ _]
    exact (pow_two _).symm
  have hvec (w : ι → ℂ) (i : ι) : (M⁻¹ *ᵥ w) i = M⁻¹ i i * w i := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique]
    rw [show (default : ι) = i from Subsingleton.elim _ _]
  rw [MvPolynomial.eval_rename]
  have hx :
      Sum.elim (fun ij => (M⁻¹.transpose * (1 : Matrix ι ι ℂ) * M⁻¹) ij.1 ij.2)
        (fun tc : Fin n × (Fin r × ι) => v tc.1 tc.2.1 tc.2.2) ∘ Sum.map (fun i => (i, i)) id =
      Sum.elim (fun i => (M⁻¹ i i) ^ 2) (fun tc : Fin n × (Fin r × ι) => v tc.1 tc.2.1 tc.2.2) := by
    funext s
    cases s with
    | inl i => exact hdiag i
    | inr tc => rfl
  rw [hx, hP]
  apply congrArg f
  funext j c i
  exact (hvec (v j c) i).symm

end HodgeLean.Foundations.Program
