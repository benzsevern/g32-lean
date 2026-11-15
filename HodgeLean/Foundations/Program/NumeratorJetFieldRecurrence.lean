import HodgeLean.Foundations.Program.NumeratorJetMatrixRecurrence

/-! # Finite coefficient formula for the actual Schlesinger field -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Geometric coefficients of the affine pole ratio. -/
def b65e_poleRatioCoeff (p : Fin 12 → ℂ) (q r : Fin 4 ⊕ Fin 12) (n : ℕ) : ℂ :=
  ((b65p_velocity p q - b65p_velocity p r) /
    (b65p_poles p 0 q - b65p_poles p 0 r)) *
  (-(b65p_velocity p q - b65p_velocity p r) /
    (b65p_poles p 0 q - b65p_poles p 0 r)) ^ n

/-- The finite convolution field on arrays of residue coefficients. -/
def b65e_fieldCoeff (p : Fin 12 → ℂ)
    (C : ℕ → Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (n : ℕ) (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) : ℂ :=
  ∑ r : Fin 4 ⊕ Fin 12, if r = q then 0 else
    ∑ a ∈ Finset.range (n + 1), b65e_poleRatioCoeff p q r a *
      ((∑ k : Fin 4, ∑ b ∈ Finset.range (n - a + 1),
        C b r i k * C (n - a - b) q k j) -
       (∑ k : Fin 4, ∑ b ∈ Finset.range (n - a + 1),
        C b q i k * C (n - a - b) r k j))

/-- Off-diagonal summands of the actual field have the finite convolution coefficients. -/
theorem b65e_fieldTerm_coeff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {P : (Fin 4 ⊕ Fin 12) → Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ q i j, HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) (P q i j) 0)
    (q r : Fin 4 ⊕ Fin 12) (hqr : q ≠ r) (i j : Fin 4)
    {S : FormalMultilinearSeries ℂ ℂ ℂ}
    (hS : HasFPowerSeriesAt (fun θ ↦
      ((b65p_velocity p q - b65p_velocity p r) /
        (b65p_poles p θ q - b65p_poles p θ r)) *
      (b65q_res O.residue θ r * b65q_res O.residue θ q -
        b65q_res O.residue θ q * b65q_res O.residue θ r) i j) S 0) (n : ℕ) :
    S.coeff n = ∑ a ∈ Finset.range (n + 1), b65e_poleRatioCoeff p q r a *
      ((∑ k : Fin 4, ∑ b ∈ Finset.range (n - a + 1),
        (P r i k).coeff b * (P q k j).coeff (n - a - b)) -
       (∑ k : Fin 4, ∑ b ∈ Finset.range (n - a + 1),
        (P q i k).coeff b * (P r k j).coeff (n - a - b))) := by
  obtain ⟨U, hU, hc⟩ := b65e_poleRatio_series p O q r hqr
  have hr := b65q_MatAn.res O r
  have hq := b65q_MatAn.res O q
  obtain ⟨T, hT⟩ := ((hr.mul hq).sub (hq.mul hr)) i j 0
    (Metric.mem_ball_self O.radius_pos)
  rw [b65e_mul_coeff hU hT hS]
  apply Finset.sum_congr rfl
  intro a _
  rw [hc, b65e_matrix_commutator_coeff (hP r) (hP q) i j hT]
  rfl

/-- The actual field series is the finite convolution field on the residue series. -/
theorem b65e_field_coeff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {P : (Fin 4 ⊕ Fin 12) → Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ q i j, HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) (P q i j) 0)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) {S : FormalMultilinearSeries ℂ ℂ ℂ}
    (hS : HasFPowerSeriesAt (fun θ ↦ b65e_fieldEntry p O.residue θ q i j) S 0)
    (n : ℕ) :
    S.coeff n = b65e_fieldCoeff p (fun a r i j ↦ (P r i j).coeff a) n q i j := by
  let f (r : Fin 4 ⊕ Fin 12) (θ : ℂ) : ℂ := if r = q then 0 else
    ((b65p_velocity p q - b65p_velocity p r) /
      (b65p_poles p θ q - b65p_poles p θ r)) *
    (b65q_res O.residue θ r * b65q_res O.residue θ q -
      b65q_res O.residue θ q * b65q_res O.residue θ r) i j
  have han (r : Fin 4 ⊕ Fin 12) : AnalyticAt ℂ (f r) 0 := by
    by_cases hrq : r = q
    · simpa only [f, hrq, ite_true] using (analyticAt_const (v := (0 : ℂ)) (x := (0 : ℂ)))
    · obtain ⟨U, hU, _⟩ := b65e_poleRatio_series p O q r (Ne.symm hrq)
      have hr := b65q_MatAn.res O r
      have hq := b65q_MatAn.res O q
      convert hU.analyticAt.mul
        (((hr.mul hq).sub (hq.mul hr)) i j 0 (Metric.mem_ball_self O.radius_pos)) using 1
      ext θ
      simp only [f, hrq, ite_false, Pi.mul_apply]
  choose T hT using han
  rw [b65e_sum_coeff Finset.univ (fun r _ ↦ hT r) hS]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrq : r = q
  · rw [ite_eq_left hrq]
    have ht : HasFPowerSeriesAt (fun _ : ℂ ↦ (0 : ℂ)) (T r) 0 := by
      simpa only [f, hrq, ite_true] using hT r
    have he := ht.eq_formalMultilinearSeries
      (hasFPowerSeriesAt_const (c := (0 : ℂ)) (e := (0 : ℂ)))
    rw [he]
    cases n <;> simp [FormalMultilinearSeries.coeff, constFormalMultilinearSeries]
  · rw [ite_eq_right hrq]
    exact b65e_fieldTerm_coeff p O hP q r (Ne.symm hrq) i j
      (by simpa only [f, hrq, ite_false] using hT r) n

/-- Every analytic choice of residue series satisfies the explicit matrix recurrence. -/
theorem b65e_residue_coeff_recurrence (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {P : (Fin 4 ⊕ Fin 12) → Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ q i j, HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) (P q i j) 0)
    (n : ℕ) (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) :
    (n + 1 : ℂ) * (P q i j).coeff (n + 1) =
      b65e_fieldCoeff p (fun a r i j ↦ (P r i j).coeff a) n q i j := by
  obtain ⟨U, V, hU, hV, hc⟩ := b65e_residue_series_recurrence p O q i j
  have he := hU.eq_formalMultilinearSeries (hP q i j)
  rw [he] at hc
  rw [← hc n]
  exact b65e_field_coeff p O hP q i j hV n

/-- The order-n field uses residue coefficients only through order n. -/
theorem b65e_fieldCoeff_congr (p : Fin 12 → ℂ)
    {C D : ℕ → Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ} (n : ℕ)
    (h : ∀ a ≤ n, C a = D a) : b65e_fieldCoeff p C n = b65e_fieldCoeff p D n := by
  funext q i j
  unfold b65e_fieldCoeff
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · rfl
  · apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha
    congr 1
    congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;>
      apply Finset.sum_congr rfl <;> intro b hb <;>
      have hb' : b ≤ n - a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb
    all_goals rw [h b (by omega), h (n - a - b) (by omega)]

/-- A finite coefficient array satisfying the initial value and field recurrence agrees with
any analytic residue series through the certified order. -/
theorem b65e_residue_coeff_of_recurrence (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (C : ℕ → Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ) (N : ℕ)
    (hbase : C 0 = fun q ↦ b65q_mat (b65p_initialResidue q))
    (hstep : ∀ n < N, ∀ q i j,
      (n + 1 : ℂ) * C (n + 1) q i j = b65e_fieldCoeff p C n q i j)
    {P : (Fin 4 ⊕ Fin 12) → Fin 4 → Fin 4 → FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ q i j, HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) (P q i j) 0) :
    ∀ n ≤ N, ∀ q i j, (P q i j).coeff n = C n q i j := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn q i j
    cases n with
    | zero =>
      calc
        (P q i j).coeff 0 = b65q_res O.residue 0 q i j := (hP q i j).coeff_zero _
        _ = C 0 q i j := by rw [hbase]; simp only [b65q_res, O.residue_zero]
    | succ n =>
      apply mul_left_cancel₀ (show (n + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      rw [b65e_residue_coeff_recurrence p O hP n q i j]
      have hc : ∀ a ≤ n, (fun r i j ↦ (P r i j).coeff a) = C a := by
        intro a ha
        funext r i j
        exact ih a (by omega) (by omega) r i j
      rw [b65e_fieldCoeff_congr p n hc]
      exact (hstep n (by omega) q i j).symm

end HodgeLean.Foundations.Program
