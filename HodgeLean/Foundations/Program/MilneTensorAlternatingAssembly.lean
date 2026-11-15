import HodgeLean.Foundations.Program.MilneTensorAlternatingGluing
import HodgeLean.Foundations.Program.MilneTensorReindexPolynomial
import HodgeLean.Foundations.Program.MilneTensorMultilinearDensity
import HodgeLean.Foundations.Program.MilneTensorMatrixOrbit

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [LinearOrder ι] [Fintype ι]

set_option maxHeartbeats 400000 in
theorem m1b_alternating_orbit_polynomial_from_numerator {r n : ℕ}
    (B : Matrix ι ι ℂ) (hB : ∀ i j, B j i = -B i j) (hdB : B.det ≠ 0)
    (p₀ p₁ : {p : ι × ι // p.1 < p.2}) (hp : p₀ ≠ p₁)
    (e : ι ≃ ι) (he₀ : e p₀.val.1 = p₁.val.1) (he₁ : e p₀.val.2 = p₁.val.2)
    (hiB : B p₀.val.1 p₀.val.2 ≠ 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B.toBilin', ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v)
    (a : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ) (k : ℕ)
    (ha : ∀ Q : Matrix ι ι ℂ, (∀ i j, Q j i = -Q i j) → (∀ i, Q i i = 0) →
      Q.det ≠ 0 → Q p₀.val.1 p₀.val.2 ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) a =
            Q p₀.val.1 p₀.val.2 ^ k * m1b_totalOrbitExtension B.toBilin' f Q.toBilin' v) :
    ∃ p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun ij => (M⁻¹.transpose * B * M⁻¹) ij.1 ij.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) p = f (fun t c => M⁻¹ *ᵥ v t c) := by
  have hb : ∀ Q : Matrix ι ι ℂ, (∀ i j, Q j i = -Q i j) → (∀ i, Q i i = 0) →
      Q.det ≠ 0 → Q p₁.val.1 p₁.val.2 ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) (m1b_reindexFormVectorPolynomial e a) =
            Q p₁.val.1 p₁.val.2 ^ k * m1b_totalOrbitExtension B.toBilin' f Q.toBilin' v := by
    intro Q hQ hdiag hd hi v
    rw [m1b_reindexFormVectorPolynomial_eval]
    have hd' : Matrix.det (fun i j => Q (e i) (e j)) ≠ 0 := by
      change (Matrix.reindex e.symm e.symm Q).det ≠ 0
      rw [Matrix.det_reindex_self]
      exact hd
    have he := ha (fun i j => Q (e i) (e j)) (fun i j => hQ (e i) (e j))
      (fun i => hdiag (e i)) hd' (by simpa only [he₀, he₁] using hi)
      (fun t c i => v t c (e i))
    rw [m1b_totalOrbitExtension_reindex B Q f hf e v] at he
    simpa only [he₀, he₁] using he
  obtain ⟨p, hpoly⟩ := m1b_alternating_two_chart_polynomial p₀ p₁ hp B hB
    (fun i => CharZero.eq_neg_self_iff.mp (hB i i)) hdB a
    (m1b_reindexFormVectorPolynomial e a) k k
    (fun Q v => m1b_totalOrbitExtension B.toBilin' f Q.toBilin'
      (fun t c i => v (t, c, i)))
    (fun Q hQ hdiag hd hi v => ha Q hQ hdiag hd hi (fun t c i => v (t, c, i)))
    (fun Q hQ hdiag hd hi v => hb Q hQ hdiag hd hi (fun t c i => v (t, c, i)))
  refine ⟨p, m1b_multilinear_orbit_extension_of_local B f p p₀.val.1 p₀.val.2 hiB ?_⟩
  intro M hM hi v
  have hBT : B.transpose = -B := by ext i j; exact hB i j
  have hQT : (M⁻¹.transpose * B * M⁻¹).transpose = -(M⁻¹.transpose * B * M⁻¹) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hBT,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hQ (i j : ι) : (M⁻¹.transpose * B * M⁻¹) j i = -(M⁻¹.transpose * B * M⁻¹) i j :=
    congrArg (fun Q : Matrix ι ι ℂ => Q i j) hQT
  have hdQ : (M⁻¹.transpose * B * M⁻¹).det ≠ 0 := by
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hM) hdB) (inv_ne_zero hM)
  have he := hpoly (M⁻¹.transpose * B * M⁻¹) hQ
    (fun i => CharZero.eq_neg_self_iff.mp (hQ i i)) hdQ (Or.inl hi)
    (fun tc => v tc.1 tc.2.1 tc.2.2)
  exact he.trans (m1b_totalOrbitExtension_matrix_eval B f hf M hM v)

end HodgeLean.Foundations.Program
