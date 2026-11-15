import HodgeLean.Foundations.Program.MilneTensorReindexPolynomial
import HodgeLean.Foundations.Program.MilneTensorMultilinearDensity

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 400000 in
theorem m1b_symmetric_polynomial_from_numerator {r n : ℕ}
    (B : Matrix ι ι ℂ) (hsB : ∀ s t, B s t = B t s) (hdB : B.det ≠ 0)
    (i j : ι) (hij : i ≠ j) (hiB : B i i ≠ 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (F : Matrix ι ι ℂ → (Fin n → Fin r → ι → ℂ) → ℂ)
    (hF : ∀ (e : ι ≃ ι) (Q : Matrix ι ι ℂ), (∀ s t, Q s t = Q t s) → Q.det ≠ 0 →
      ∀ v : Fin n → Fin r → ι → ℂ, F (fun s t => Q (e s) (e t)) (fun t c s => v t c (e s)) = F Q v)
    (hOrbit : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
      F (M⁻¹.transpose * B * M⁻¹) v = f (fun t c => M⁻¹ *ᵥ v t c))
    (a : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ) (k : ℕ)
    (ha : ∀ (Q : Matrix ι ι ℂ), (∀ s t, Q s t = Q t s) → Q.det ≠ 0 → Q i i ≠ 0 →
      ∀ v : Fin n → Fin r → ι → ℂ, MvPolynomial.eval (Sum.elim (fun st => Q st.1 st.2)
        (fun tc => v tc.1 tc.2.1 tc.2.2)) a = Q i i ^ k * F Q v) :
    ∃ p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun st => (M⁻¹.transpose * B * M⁻¹) st.1 st.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) p = f (fun t c => M⁻¹ *ᵥ v t c) := by
  let e := Equiv.swap i j
  have hb := m1b_symmetric_reindexed_numerator e i a k F ha (hF e)
  simp only [e, Equiv.swap_apply_left] at hb
  obtain ⟨p, hp⟩ := m1b_symmetric_two_chart_polynomial i j hij a
    (m1b_reindexFormVectorPolynomial e a) k k
    (fun Q v => F Q (fun t c s => v (t, c, s)))
    (fun Q hs hd hi v => ha Q hs hd hi (fun t c s => v (t, c, s)))
    (fun Q hs hd hj v => hb Q hs hd hj (fun t c s => v (t, c, s)))
  refine ⟨p, m1b_multilinear_orbit_extension_of_local B f p i i hiB ?_⟩
  intro M hM hi v
  have hBT : B.transpose = B := by
    ext s t
    exact hsB t s
  have hsQ : ∀ s t, (M⁻¹.transpose * B * M⁻¹) s t =
      (M⁻¹.transpose * B * M⁻¹) t s := by
    have ht : (M⁻¹.transpose * B * M⁻¹).transpose = M⁻¹.transpose * B * M⁻¹ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBT,
        Matrix.mul_assoc]
    intro s t
    exact (congrArg (fun Q : Matrix ι ι ℂ => Q s t) ht).symm
  have hdQ : (M⁻¹.transpose * B * M⁻¹).det ≠ 0 := by
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hM) hdB) (inv_ne_zero hM)
  have he := hp (M⁻¹.transpose * B * M⁻¹) hsQ hdQ (Or.inl hi)
    (fun tc => v tc.1 tc.2.1 tc.2.2)
  exact he.trans (hOrbit M hM v)

end HodgeLean.Foundations.Program
