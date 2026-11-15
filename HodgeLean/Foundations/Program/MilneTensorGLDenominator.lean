import HodgeLean.Foundations.Program.MilneTensorChartSubstitution
import HodgeLean.Foundations.Program.MilneTensorCoordinatePolynomial

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_det_smul_inverse (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    M.det • M⁻¹ = M.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hM, one_smul]

theorem m1b_inverse_congruence_denominator (M B : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    M.det ^ 2 • (M⁻¹.transpose * B * M⁻¹) = M.adjugate.transpose * B * M.adjugate := by
  have h := congrArg (fun N : Matrix ι ι ℂ => N.transpose * B * N)
    (m1b_det_smul_inverse M hM)
  simpa only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two] using h

theorem m1b_form_polynomial_GL_denominator {σ : Type*} {r n : ℕ}
    (T : Matrix ι ι (MvPolynomial σ ℂ)) (B : Matrix ι ι ℂ)
    (v : Fin n → Fin r → ι → MvPolynomial σ ℂ)
    (p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ) :
    ∃ k : ℕ, ∃ q : MvPolynomial σ ℂ, ∀ x, MvPolynomial.eval x T.det ≠ 0 →
      MvPolynomial.eval x T.det ^ k * MvPolynomial.eval
        (Sum.elim (fun ij =>
          (((MvPolynomial.eval x).mapMatrix T)⁻¹.transpose * B *
            ((MvPolynomial.eval x).mapMatrix T)⁻¹) ij.1 ij.2)
          (fun jc => MvPolynomial.eval x (v jc.1 jc.2.1 jc.2.2))) p =
            MvPolynomial.eval x q := by
  apply m1b_polynomial_chart_denominator
  intro z
  cases z with
  | inl ij =>
    let N := T.adjugate.transpose * B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) * T.adjugate
    refine ⟨2, N ij.1 ij.2, ?_⟩
    intro x hx
    let ev := MvPolynomial.eval x
    have hdet : ev T.det = (ev.mapMatrix T).det := ev.map_det T
    have hc : ev.mapMatrix (B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)) = B := by
      ext i j
      exact MvPolynomial.eval_C _
    have hN : ev.mapMatrix N =
        (ev.mapMatrix T).adjugate.transpose * B * (ev.mapMatrix T).adjugate := by
      dsimp only [N]
      rw [map_mul, map_mul]
      change (ev.mapMatrix T.adjugate).transpose * ev.mapMatrix (B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)) *
        ev.mapMatrix T.adjugate = _
      rw [ev.map_adjugate, hc]
    have h := congrArg (fun M : Matrix ι ι ℂ => M ij.1 ij.2)
      (m1b_inverse_congruence_denominator (ev.mapMatrix T) B (by rw [← hdet]; exact hx))
    rw [← hN] at h
    change ev T.det ^ 2 *
      (((ev.mapMatrix T)⁻¹).transpose * B * (ev.mapMatrix T)⁻¹) ij.1 ij.2 = ev (N ij.1 ij.2)
    rw [hdet]
    exact h
  | inr jc =>
    refine ⟨0, v jc.1 jc.2.1 jc.2.2, ?_⟩
    intro x _
    simp only [pow_zero, one_mul, Sum.elim_inr]

theorem m1b_vector_polynomial_GL_denominator {σ : Type*} {r n : ℕ}
    (T : Matrix ι ι (MvPolynomial σ ℂ))
    (v : Fin n → Fin r → ι → MvPolynomial σ ℂ)
    (p : MvPolynomial (Fin n × (Fin r × ι)) ℂ) :
    ∃ k : ℕ, ∃ q : MvPolynomial σ ℂ, ∀ x, MvPolynomial.eval x T.det ≠ 0 →
      MvPolynomial.eval x T.det ^ k * MvPolynomial.eval
        (fun jc => (((MvPolynomial.eval x).mapMatrix T)⁻¹ *ᵥ
          (fun i => MvPolynomial.eval x (v jc.1 jc.2.1 i))) jc.2.2) p =
            MvPolynomial.eval x q := by
  apply m1b_polynomial_chart_denominator
  intro jc
  refine ⟨1, ∑ j, T.adjugate jc.2.2 j * v jc.1 jc.2.1 j, ?_⟩
  intro x hx
  let ev := MvPolynomial.eval x
  have hdet : ev T.det = (ev.mapMatrix T).det := ev.map_det T
  have h := congrArg (fun M : Matrix ι ι ℂ =>
    (M *ᵥ (fun j => ev (v jc.1 jc.2.1 j))) jc.2.2)
      (m1b_det_smul_inverse (ev.mapMatrix T) (by rw [← hdet]; exact hx))
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul] at h
  have hn : ev (∑ j, T.adjugate jc.2.2 j * v jc.1 jc.2.1 j) =
      ((ev.mapMatrix T).adjugate *ᵥ (fun j => ev (v jc.1 jc.2.1 j))) jc.2.2 := by
    rw [← ev.map_adjugate T]
    change ev (∑ j, T.adjugate jc.2.2 j * v jc.1 jc.2.1 j) =
      ∑ j, ev (T.adjugate jc.2.2 j) * ev (v jc.1 jc.2.1 j)
    simp only [map_sum, map_mul]
  change ev T.det ^ 1 * (((ev.mapMatrix T)⁻¹) *ᵥ
    (fun j => ev (v jc.1 jc.2.1 j))) jc.2.2 = _
  rw [pow_one, hdet, hn]
  exact h

theorem m1b_eval_adjugate_congruence {σ : Type*}
    (T : Matrix ι ι (MvPolynomial σ ℂ)) (B : Matrix ι ι ℂ) (x : σ → ℂ) (i j : ι) :
    MvPolynomial.eval x ((T.adjugate.transpose * B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) * T.adjugate) i j) =
      (((MvPolynomial.eval x).mapMatrix T).adjugate.transpose * B *
        ((MvPolynomial.eval x).mapMatrix T).adjugate) i j := by
  let ev := MvPolynomial.eval x
  have hc : ev.mapMatrix (B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)) = B := by
    ext a b
    exact MvPolynomial.eval_C _
  have hN : ev.mapMatrix (T.adjugate.transpose * B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) * T.adjugate) =
      (ev.mapMatrix T).adjugate.transpose * B * (ev.mapMatrix T).adjugate := by
    rw [map_mul, map_mul]
    change (ev.mapMatrix T.adjugate).transpose * ev.mapMatrix (B.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)) *
      ev.mapMatrix T.adjugate = _
    rw [ev.map_adjugate, hc]
  exact congrArg (fun M : Matrix ι ι ℂ => M i j) hN

end HodgeLean.Foundations.Program
