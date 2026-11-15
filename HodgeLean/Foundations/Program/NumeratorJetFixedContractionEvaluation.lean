import HodgeLean.Foundations.Program.NumeratorJetFixedContractions

/-! # Weighted trace interpretation of the finite rational contractions -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Products of two coordinate arrays are summed by the degree-ten power moments. -/
theorem b65e_coordinateProduct_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (U V : Fin 6 → ℚ) :
    (∑ x ∈ b65q_fibreSet e,
      (∑ c : Fin 6, (U c : ℂ) * p x ^ (c : ℕ)) *
      (∑ d : Fin 6, (V d : ℂ) * p x ^ (d : ℕ))) =
    ∑ c : Fin 6, ∑ d : Fin 6,
      (U c : ℂ) * (V d : ℂ) *
        (b65e_powerMomentQ ⟨c.val + d.val, by omega⟩ e : ℂ) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hterm (x : Fin 12) :
      (U c : ℂ) * p x ^ (c : ℕ) * ((V d : ℂ) * p x ^ (d : ℕ)) =
      ((U c : ℂ) * (V d : ℂ)) * p x ^ (c.val + d.val) := by
    rw [pow_add]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, b65e_powerMoment_sum p O ⟨c.val + d.val, by omega⟩ e]

/-- The finite weighted-moving array equals the weighted sum over the moving labels. -/
theorem b65e_weightedMovingQ_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (b : Fin 8) (e : Fin 2) (k : Fin 4) (i j : Fin 4) :
    ∑ x ∈ b65q_fibreSet e,
      b65e_poleRatioCoeff p (.inl k) (.inr x) n *
        b65e_residueJet p b (.inr x) i j =
      (b65e_weightedMovingQ n b e k i j : ℂ) := by
  have heval (x : Fin 12) (hx : x ∈ b65q_fibreSet e) :
      b65e_poleRatioCoeff p (.inl k) (.inr x) n *
        b65e_residueJet p b (.inr x) i j =
      (∑ c : Fin 6, (b65e_fixedWeightCoeffQ n e k c : ℂ) * p x ^ (c : ℕ)) *
      (∑ d : Fin 6, (b65e_movingJet b e d i j : ℂ) * p x ^ (d : ℕ)) := by
    rw [← b65e_fixedWeight_poleRatioCoeff p O e k x hx n]
    have he := (Finset.mem_filter.mp hx).2
    simp only [b65e_reducedFixedWeightQ, eval₂_finsetSum, eval₂_mul, eval₂_C,
      eval₂_pow, eval₂_X, Rat.coe_castHom, b65e_residueJet, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, he]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [Finset.sum_congr rfl heval, b65e_coordinateProduct_sum p O e]
  unfold b65e_weightedMovingQ b65e_weightMomentQ
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

end HodgeLean.Foundations.Program
