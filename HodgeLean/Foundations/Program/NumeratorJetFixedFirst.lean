import HodgeLean.Foundations.Program.NumeratorJetFirstOrder

/-! # First Taylor coefficients at the fixed poles -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Grouping the initial Schlesinger field by fibre gives the rational first recursion. -/
theorem b65e_fieldEntry_fixed_zero (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (k : Fin 4) (i j : Fin 4) :
    b65e_fieldEntry p O.residue 0 (Sum.inl k) i j =
      (b65e_fixedFirstQ k i j : ℂ) := by
  have hfibre (x : Fin 12) :
      b65q_fibreValue (b65q_fibreIndex x) = b65p_fibre x := by
    fin_cases x <;> decide +kernel
  unfold b65e_fieldEntry
  rw [Fintype.sum_sum_type]
  have hz : (∑ r : Fin 4, if (Sum.inl r : Fin 4 ⊕ Fin 12) = Sum.inl k then (0 : ℂ) else
      ((b65p_velocity p (Sum.inl k) - b65p_velocity p (Sum.inl r)) /
        (b65p_poles p 0 (Sum.inl k) - b65p_poles p 0 (Sum.inl r))) *
      (b65q_res O.residue 0 (Sum.inl r) * b65q_res O.residue 0 (Sum.inl k) -
        b65q_res O.residue 0 (Sum.inl k) * b65q_res O.residue 0 (Sum.inl r)) i j) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    split_ifs <;> simp only [b65p_velocity, Sum.elim_inl, Pi.zero_apply,
      sub_self, zero_div, zero_mul]
  rw [hz, zero_add]
  simp only [reduceCtorEq, ite_false, b65p_velocity, b65p_poles, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, zero_mul, add_zero, zero_sub,
    b65q_res_zero_inl, b65q_res_zero_inr]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  have hF (e : Fin 2) :
      (∑ x ∈ Finset.univ.filter (fun x ↦ b65q_fibreIndex x = e),
        (-b65p_V (b65p_fibre x) (p x) / (b65p_fixedPole k - p x)) *
        ((b65q_BQ (b65q_fibreIndex x)).map (Rat.castHom ℂ) *
          (b65q_fixedResQ k).map (Rat.castHom ℂ) -
        (b65q_fixedResQ k).map (Rat.castHom ℂ) *
          (b65q_BQ (b65q_fibreIndex x)).map (Rat.castHom ℂ)) i j) =
      (b65e_velocityMoment e k : ℂ) *
        ((b65q_BQ e).map (Rat.castHom ℂ) * (b65q_fixedResQ k).map (Rat.castHom ℂ) -
          (b65q_fixedResQ k).map (Rat.castHom ℂ) * (b65q_BQ e).map (Rat.castHom ℂ)) i j := by
    rw [← b65e_velocityMoment_sum p O e k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    rw [← hfibre x, he]
    congr 1
    rw [← neg_sub (p x) (b65p_fixedPole k), neg_div_neg_eq]
  simp only [Fin.sum_univ_two] at *
  rw [hF 0, hF 1]
  simp only [b65e_fixedFirstQ, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.map_apply,
    Matrix.mul_apply, Rat.coe_castHom]
  push_cast
  ring

/-- Every analytic residue series has the stored order-one coefficient at a fixed pole. -/
theorem b65e_fixed_residue_coeff_one (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (k : Fin 4) (i j : Fin 4) {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ (Sum.inl k) i j) P 0) :
    P.coeff 1 = (b65e_fixedJet 1 k i j : ℂ) := by
  have h := hP.hasDerivAt.unique
    (b65e_residue_hasDerivAt p O (Sum.inl k) i j (Metric.mem_ball_self O.radius_pos))
  change P.coeff 1 = b65e_fieldEntry p O.residue 0 (Sum.inl k) i j at h
  rw [h, b65e_fieldEntry_fixed_zero p O k i j, b65e_fixedFirstQ_table]

end HodgeLean.Foundations.Program
