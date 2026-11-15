import HodgeLean.Foundations.Program.MilneTensorPairedNumerator

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_pair_intrinsic_numerator {d r n : ℕ}
    (p : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
      (Fin n × ((Fin r × Fin 2) ⊕ (Fin r × Fin d)))) ℂ) :
    ∃ k : ℕ, ∃ q : MvPolynomial (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕
        (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) ℂ,
      ∀ (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × (Fin d → ℂ))) (a : ℂˣ),
        Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val →
        ∀ v : Fin n → Fin r → (Fin 2 → ℂ) × (Fin d → ℂ),
          a.val ^ k * MvPolynomial.eval (Sum.elim
            (Sum.elim (fun _ => a.val)
              (fun ij => m1b_pairSchur Q a (Pi.single ij.1 1) (Pi.single ij.2 1)))
            (fun jc => Sum.elim
              (fun ci => ((v jc.1 ci.1).1 + m1b_pairShear Q a (v jc.1 ci.1).2) ci.2)
              (fun ci => (v jc.1 ci.1).2 ci.2) jc.2)) p =
            MvPolynomial.eval (m1b_pairFormPoint Q v) q := by
  obtain ⟨k, q, hq⟩ := m1b_alternating_chart_numerator
    (τ := ((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕ (Fin n × (Fin r × (Fin 2 ⊕ Fin d))))
    (MvPolynomial.X (Sum.inl (Sum.inl 0, Sum.inl 1)))
    (fun i => MvPolynomial.X (Sum.inl (Sum.inl 0, Sum.inr i)))
    (fun i => MvPolynomial.X (Sum.inl (Sum.inl 1, Sum.inr i)))
    (fun i j => MvPolynomial.X (Sum.inl (Sum.inr i, Sum.inr j)))
    (fun j c i => MvPolynomial.X (Sum.inr (j, c, Sum.inl i)))
    (fun j c i => MvPolynomial.X (Sum.inr (j, c, Sum.inr i))) p
  refine ⟨k, q, ?_⟩
  intro Q a ha v
  have h := hq (m1b_pairFormPoint Q v) (by
    simpa only [MvPolynomial.eval_X, m1b_pairFormPoint, m1b_pairBasisVector,
      Sum.elim_inl, ha] using a.ne_zero)
  simp only [MvPolynomial.eval_X, m1b_pairFormPoint, m1b_pairBasisVector,
    Sum.elim_inl, Sum.elim_inr, ha] at h
  have hcross (j : Fin 2) (w : Fin d → ℂ) :
      (∑ i, m1b_pairCross Q j (Pi.single i 1) * w i) = m1b_pairCross Q j w := by
    rw [m1b_dual_apply_coordinates d (m1b_pairCross Q j) w]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  convert h using 1
  congr 2
  congr 1
  funext z
  rcases z with ((z | ij) | ⟨j, ci | ci⟩)
  · rfl
  · change Q (0, Pi.single ij.1 1) (0, Pi.single ij.2 1) + a.inv *
      (m1b_pairCross Q 1 (Pi.single ij.1 1) * m1b_pairCross Q 0 (Pi.single ij.2 1) -
        m1b_pairCross Q 0 (Pi.single ij.1 1) * m1b_pairCross Q 1 (Pi.single ij.2 1)) =
      Q (0, Pi.single ij.1 1) (0, Pi.single ij.2 1) +
      (m1b_pairCross Q 1 (Pi.single ij.1 1) * m1b_pairCross Q 0 (Pi.single ij.2 1) -
        m1b_pairCross Q 0 (Pi.single ij.1 1) * m1b_pairCross Q 1 (Pi.single ij.2 1)) / a.val
    rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    ring
  · change ((v j ci.1).1 + m1b_pairShear Q a (v j ci.1).2) ci.2 =
      (v j ci.1).1 ci.2 +
        (if ci.2 = 0 then -(∑ i, m1b_pairCross Q 1 (Pi.single i 1) * (v j ci.1).2 i)
          else ∑ i, m1b_pairCross Q 0 (Pi.single i 1) * (v j ci.1).2 i) / a.val
    rw [hcross, hcross]
    by_cases hc : ci.2 = 0 <;>
      simp only [Pi.add_apply, m1b_pairShear, LinearMap.pi_apply, hc, ite_true, ite_false,
        LinearMap.smul_apply, smul_eq_mul]
    all_goals
      rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, div_eq_mul_inv]
      ring
  · rfl
  all_goals rfl

end HodgeLean.Foundations.Program
