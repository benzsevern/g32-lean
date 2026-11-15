import HodgeLean.Foundations.Program.MilneTensorChartSubstitution
import HodgeLean.Foundations.Program.MilneTensorPivotSchur

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_symmetric_chart_numerator {τ : Type*} {d r n : ℕ}
    (a : MvPolynomial τ ℂ) (b : Fin d → MvPolynomial τ ℂ)
    (D : Matrix (Fin d) (Fin d) (MvPolynomial τ ℂ))
    (x : Fin n → Fin r → MvPolynomial τ ℂ)
    (y : Fin n → Fin r → Fin d → MvPolynomial τ ℂ)
    (p : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
      (Fin n × (Fin r ⊕ (Fin r × Fin d)))) ℂ) :
    ∃ k : ℕ, ∃ q : MvPolynomial τ ℂ, ∀ z, MvPolynomial.eval z a ≠ 0 →
      MvPolynomial.eval z a ^ k * MvPolynomial.eval
        (Sum.elim
          (Sum.elim (fun _ => MvPolynomial.eval z a)
            (fun ij => MvPolynomial.eval z (D ij.1 ij.2) -
              MvPolynomial.eval z (b ij.1) * MvPolynomial.eval z (b ij.2) /
                MvPolynomial.eval z a))
          (fun jc => Sum.elim
            (fun c => MvPolynomial.eval z (x jc.1 c) +
              (∑ i, MvPolynomial.eval z (b i) * MvPolynomial.eval z (y jc.1 c i)) /
                MvPolynomial.eval z a)
            (fun ci => MvPolynomial.eval z (y jc.1 ci.1 ci.2)) jc.2)) p =
        MvPolynomial.eval z q := by
  let u : ((Unit ⊕ (Fin d × Fin d)) ⊕ (Fin n × (Fin r ⊕ (Fin r × Fin d)))) →
      MvPolynomial τ ℂ :=
    Sum.elim (Sum.elim (fun _ => a) (fun ij => D ij.1 ij.2))
      (fun jc => Sum.elim (fun c => x jc.1 c) (fun ci => y jc.1 ci.1 ci.2) jc.2)
  let v : ((Unit ⊕ (Fin d × Fin d)) ⊕ (Fin n × (Fin r ⊕ (Fin r × Fin d)))) →
      MvPolynomial τ ℂ :=
    Sum.elim (Sum.elim (fun _ => 0) (fun ij => -(b ij.1 * b ij.2)))
      (fun jc => Sum.elim (fun c => ∑ i, b i * y jc.1 c i) (fun _ => 0) jc.2)
  obtain ⟨k, q, hq⟩ := m1b_polynomial_affine_pivot_chart a u v p
  refine ⟨k, q, ?_⟩
  intro z hz
  convert hq z hz using 1
  congr 2
  congr 1
  funext j
  rcases j with ((j | ij) | ⟨j, c | ci⟩) <;>
    simp only [u, v, Sum.elim_inl, Sum.elim_inr, map_zero, zero_div, add_zero,
      map_neg, map_mul, map_sum, neg_div, sub_eq_add_neg]

theorem m1b_alternating_chart_numerator {τ : Type*} {d r n : ℕ}
    (a : MvPolynomial τ ℂ) (b c : Fin d → MvPolynomial τ ℂ)
    (D : Matrix (Fin d) (Fin d) (MvPolynomial τ ℂ))
    (x : Fin n → Fin r → Fin 2 → MvPolynomial τ ℂ)
    (y : Fin n → Fin r → Fin d → MvPolynomial τ ℂ)
    (p : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
      (Fin n × ((Fin r × Fin 2) ⊕ (Fin r × Fin d)))) ℂ) :
    ∃ k : ℕ, ∃ q : MvPolynomial τ ℂ, ∀ z, MvPolynomial.eval z a ≠ 0 →
      MvPolynomial.eval z a ^ k * MvPolynomial.eval
        (Sum.elim
          (Sum.elim (fun _ => MvPolynomial.eval z a)
            (fun ij => MvPolynomial.eval z (D ij.1 ij.2) +
              (MvPolynomial.eval z (c ij.1) * MvPolynomial.eval z (b ij.2) -
                MvPolynomial.eval z (b ij.1) * MvPolynomial.eval z (c ij.2)) /
                  MvPolynomial.eval z a))
          (fun jc => Sum.elim
            (fun ci => MvPolynomial.eval z (x jc.1 ci.1 ci.2) +
              (if ci.2 = 0 then -(∑ i, MvPolynomial.eval z (c i) *
                MvPolynomial.eval z (y jc.1 ci.1 i)) else
                ∑ i, MvPolynomial.eval z (b i) * MvPolynomial.eval z (y jc.1 ci.1 i)) /
                MvPolynomial.eval z a)
            (fun ci => MvPolynomial.eval z (y jc.1 ci.1 ci.2)) jc.2)) p =
        MvPolynomial.eval z q := by
  let u : ((Unit ⊕ (Fin d × Fin d)) ⊕
      (Fin n × ((Fin r × Fin 2) ⊕ (Fin r × Fin d)))) → MvPolynomial τ ℂ :=
    Sum.elim (Sum.elim (fun _ => a) (fun ij => D ij.1 ij.2))
      (fun jc => Sum.elim (fun ci => x jc.1 ci.1 ci.2)
        (fun ci => y jc.1 ci.1 ci.2) jc.2)
  let v : ((Unit ⊕ (Fin d × Fin d)) ⊕
      (Fin n × ((Fin r × Fin 2) ⊕ (Fin r × Fin d)))) → MvPolynomial τ ℂ :=
    Sum.elim (Sum.elim (fun _ => 0) (fun ij => c ij.1 * b ij.2 - b ij.1 * c ij.2))
      (fun jc => Sum.elim (fun ci => if ci.2 = 0 then -(∑ i, c i * y jc.1 ci.1 i)
        else ∑ i, b i * y jc.1 ci.1 i) (fun _ => 0) jc.2)
  obtain ⟨k, q, hq⟩ := m1b_polynomial_affine_pivot_chart a u v p
  refine ⟨k, q, ?_⟩
  intro z hz
  convert hq z hz using 1
  congr 2
  congr 1
  funext j
  rcases j with ((j | ij) | ⟨j, ci | ci⟩)
  · simp only [u, v, Sum.elim_inl, map_zero, zero_div, add_zero]
  · simp only [u, v, Sum.elim_inl, Sum.elim_inr, map_sub, map_mul]
  · by_cases hi : ci.2 = 0 <;>
      simp only [u, v, Sum.elim_inr, Sum.elim_inl, hi, ite_true, ite_false,
        map_neg, map_sum, map_mul]
  · simp only [u, v, Sum.elim_inr, map_zero, zero_div, add_zero]

end HodgeLean.Foundations.Program
