import HodgeLean.Foundations.Program.NumeratorJetTensorWeightEvaluation
import HodgeLean.Foundations.Program.NumeratorJetDefs

/-! # Finite source moments for the certified moving weights -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Source trace of a tensor-coordinate array multiplied by one source monomial. -/
def b65e_tensorSourceMomentQ (d : Fin 2) (u : Fin 6 → Fin 6 → ℚ)
    (s c : Fin 6) : ℚ :=
  ∑ h : Fin 6, u c h * b65e_powerMomentQ ⟨h.val + s.val, by omega⟩ d

/-- Finite source moments evaluate to the sum over the record's labelled roots. -/
theorem b65e_tensorSourceMomentQ_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (d : Fin 2) (u : Fin 6 → Fin 6 → ℚ) (s : Fin 6) (x : ℂ) :
    ∑ y ∈ b65q_fibreSet d,
      b65e_tensorCoordinateEvalQ u x (p y) * p y ^ (s : ℕ) =
        b65e_coordinateEvalQ (b65e_tensorSourceMomentQ d u s) x := by
  simp only [b65e_tensorCoordinateEvalQ, b65e_coordinateEvalQ,
    b65e_tensorSourceMomentQ]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = x ^ (c : ℕ) * (u c h : ℂ) *
        (∑ y ∈ b65q_fibreSet d, p y ^ (h.val + s.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [pow_add]
      ring
    _ = _ := by
      rw [b65e_powerMoment_sum p O ⟨h.val + s.val, by omega⟩ d]
      ring

/-- Source traces of certified tensor weights times a stored moving-residue entry. -/
def b65e_tensorWeightedMovingQ (n : Fin 7) (b : Fin 8) (e d : Fin 2)
    (i j : Fin 4) (c : Fin 6) : ℚ :=
  ∑ s : Fin 6, b65e_movingJet b d s i j *
    b65e_tensorSourceMomentQ d (b65e_tensorWeightCoeffQ n e d) s c

/-- The finite weighted-moving vector gives the actual labelled source sum. -/
theorem b65e_tensorWeightedMovingQ_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (b : Fin 8) (e d : Fin 2) (i j : Fin 4) (x : ℂ) :
    b65e_coordinateEvalQ (b65e_tensorWeightedMovingQ n b e d i j) x =
      ∑ y ∈ b65q_fibreSet d,
        b65e_tensorCoordinateEvalQ (b65e_tensorWeightCoeffQ n e d) x (p y) *
          b65e_residueJet p b (.inr y) i j := by
  calc
    _ = ∑ s : Fin 6, (b65e_movingJet b d s i j : ℂ) *
        b65e_coordinateEvalQ
          (b65e_tensorSourceMomentQ d (b65e_tensorWeightCoeffQ n e d) s) x := by
      simp only [b65e_coordinateEvalQ, b65e_tensorWeightedMovingQ]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = ∑ s : Fin 6, (b65e_movingJet b d s i j : ℂ) *
        (∑ y ∈ b65q_fibreSet d,
          b65e_tensorCoordinateEvalQ (b65e_tensorWeightCoeffQ n e d) x (p y) *
            p y ^ (s : ℕ)) := by
      simp_rw [b65e_tensorSourceMomentQ_sum p O]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      have hd := (Finset.mem_filter.mp hy).2
      simp only [b65e_residueJet, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.map_apply, Rat.coe_castHom, smul_eq_mul, hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

end HodgeLean.Foundations.Program
