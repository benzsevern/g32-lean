import HodgeLean.Foundations.Program.NumeratorJetPoleWeights
import HodgeLean.Foundations.Program.NumeratorJetFixedFirst

/-! # First moving-pole residue coefficients -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Polynomial entries of the initial moving-pole field after source traces. -/
def b65e_movingFirstPolynomialQ (e : Fin 2) (i j : Fin 4) : ℚ[X] :=
  (∑ k : Fin 4, b65e_fixedWeightQ e k *
    C ((b65q_fixedResQ k * b65q_BQ e - b65q_BQ e * b65q_fixedResQ k) i j)) +
  ∑ d : Fin 2, b65e_partialTraceQ d (b65e_tensorWeightQ e d) *
    C ((b65q_BQ d * b65q_BQ e - b65q_BQ e * b65q_BQ d) i j)

/-- Fibre values attached to the final labels agree with the two-index convention. -/
theorem b65e_fibreIndex_value (x : Fin 12) :
    b65q_fibreValue (b65q_fibreIndex x) = b65p_fibre x := by
  fin_cases x <;> decide +kernel

/-- The initial field at a moving pole is evaluation of the rational polynomial field. -/
theorem b65e_fieldEntry_moving_zero (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (x : Fin 12) (i j : Fin 4) :
    b65e_fieldEntry p O.residue 0 (Sum.inr x) i j =
      (b65e_movingFirstPolynomialQ (b65q_fibreIndex x) i j).eval₂ (Rat.castHom ℂ) (p x) := by
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hroot := b65q_fibre_root O _ hx
  have hcast (A B : Matrix (Fin 4) (Fin 4) ℚ) :
      (A.map (Rat.castHom ℂ) * B.map (Rat.castHom ℂ) -
        B.map (Rat.castHom ℂ) * A.map (Rat.castHom ℂ)) i j =
      ((A * B - B * A) i j : ℂ) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Rat.coe_castHom]
    push_cast
    rfl
  unfold b65e_fieldEntry
  rw [Fintype.sum_sum_type]
  simp only [Sum.inl_ne_inr, ite_false, Sum.inr.injEq,
    b65p_velocity, b65p_poles, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, sub_zero, zero_mul, add_zero,
    b65q_res_zero_inl O, b65q_res_zero_inr O]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  have hm (d : Fin 2) :
      (∑ y ∈ Finset.univ.filter (fun y ↦ b65q_fibreIndex y = d),
        if y = x then (0 : ℂ) else
          ((b65p_V (b65p_fibre x) (p x) - b65p_V (b65p_fibre y) (p y)) / (p x - p y)) *
          ((b65q_BQ (b65q_fibreIndex y)).map (Rat.castHom ℂ) *
            (b65q_BQ (b65q_fibreIndex x)).map (Rat.castHom ℂ) -
          (b65q_BQ (b65q_fibreIndex x)).map (Rat.castHom ℂ) *
            (b65q_BQ (b65q_fibreIndex y)).map (Rat.castHom ℂ)) i j) =
      (b65e_partialTraceQ d (b65e_tensorWeightQ (b65q_fibreIndex x) d)).eval₂
          (Rat.castHom ℂ) (p x) *
        ((b65q_BQ d * b65q_BQ (b65q_fibreIndex x) -
          b65q_BQ (b65q_fibreIndex x) * b65q_BQ d) i j : ℂ) := by
    rw [← b65e_partialTraceQ_sum p O, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    have hd := (Finset.mem_filter.mp hy).2
    by_cases he : y = x
    · subst y
      simp only [ite_true, ← hd, sub_self, Matrix.zero_apply, Rat.cast_zero, mul_zero]
    · rw [ite_eq_right he, hd, hcast]
      congr 1
      rw [b65e_tensorWeightQ_eval _ _ _ _ hroot (b65q_fibre_root O d hy)]
      · rw [b65e_fibreIndex_value, ← hd, b65e_fibreIndex_value]
      · intro h
        apply he
        have hi := O.poles_injective 0 (Metric.mem_ball_self O.radius_pos)
        have hz : b65p_poles p 0 (Sum.inr x) = b65p_poles p 0 (Sum.inr y) := by
          simpa only [b65p_poles, Sum.elim_inr, zero_mul, add_zero] using h
        exact (Sum.inr.inj (hi hz)).symm
  rw [Finset.sum_congr rfl (fun d _ ↦ hm d)]
  simp only [b65e_movingFirstPolynomialQ, eval₂_add, eval₂_finsetSum, eval₂_mul,
    eval₂_C, Rat.coe_castHom]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [b65e_fixedWeightQ_eval _ _ _ hroot, b65e_fibreIndex_value]
  congr 1
  exact hcast _ _

end HodgeLean.Foundations.Program
