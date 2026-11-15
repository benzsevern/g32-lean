import HodgeLean.Foundations.Program.NumeratorJetMovingFirstEvaluation
import HodgeLean.Foundations.Program.NumeratorJetMovingContractionCertificates
import HodgeLean.Foundations.Program.NumeratorJetMovingCertificateInterface
import HodgeLean.Foundations.Program.NumeratorJetDiagonal
import HodgeLean.Foundations.Program.NumeratorJetMovingFirst
import HodgeLean.Foundations.Program.NumeratorJetFixedRecurrenceCertificates
import HodgeLean.Foundations.Program.NumeratorJetFixedContractionEvaluation
import HodgeLean.Foundations.Program.NumeratorJetFieldRecurrence
import HodgeLean.Foundations.Program.NumeratorJetFixedInverse
import HodgeLean.Foundations.Program.NumeratorJetCrossInverse
import HodgeLean.Foundations.Program.NumeratorJetPartialTrace
import HodgeLean.Foundations.Program.KernelFramesFamily
import HodgeLean.Foundations.Program.NumeratorJetFixedFirst
import HodgeLean.Foundations.Program.NumeratorJetDenominator
import HodgeLean.Foundations.Program.NumeratorJetConvolution
import HodgeLean.Foundations.Program.NumeratorJetAnalytic
import HodgeLean.Foundations.Program.NumeratorJetDefs
import HodgeLean.Foundations.Program.SchlesingerPathDefs
import HodgeLean.Papers.G32DominanceDefs

/-! # B6-5 stage 5e: the residue jets through order seven

The stored residue coefficients satisfy the actual finite Schlesinger recurrence at every pole
through order seven, hence agree with the Taylor coefficients of the analytic residues.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b65e_fixedJet_zero_table : b65e_fixedJet 0 = b65q_fixedResQ := by
  decide +kernel

theorem b65e_movingJet_zero_table : ∀ e : Fin 2, ∀ c : Fin 6,
    b65e_movingJet 0 e c = if c = 0 then b65q_BQ e else 0 := by
  decide +kernel

theorem b65e_residue_zero (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) : b65e_residueJet p 0 q = b65q_res O.residue 0 q := by
  cases q with
  | inl k =>
    rw [b65e_residueJet, b65q_res_zero_inl O, b65e_fixedJet_zero_table]
  | inr x =>
    rw [b65e_residueJet, b65q_res_zero_inr O]
    simp only [b65e_movingJet_zero_table]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro c _ hc
      rw [ite_eq_right hc]
      ext i j
      simp
    · simp

theorem b65e_residue_series_zero (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) :
    ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
        P.coeff 0 = b65e_residueJet p 0 q i j := by
  obtain ⟨P, hP⟩ := b65q_MatAn.res O q i j 0 (Metric.mem_ball_self O.radius_pos)
  refine ⟨P, hP, ?_⟩
  rw [b65e_residue_zero p O q]
  exact hP.coeff_zero (fun _ ↦ 1)

/-- Every analytic residue series has the stored first coefficient. -/
theorem b65e_residue_stored_coeff_one (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0) :
    P.coeff 1 = b65e_residueJet p 1 q i j := by
  cases q with
  | inl k => exact b65e_fixed_residue_coeff_one p O k i j hP
  | inr x => exact b65e_moving_residue_coeff_one p O x i j hP

/-- The same analytic series realizes orders zero and one at every pole. -/
theorem b65e_residue_series_one (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (q : Fin 4 ⊕ Fin 12) (i j : Fin 4) :
    ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
      ∀ n : Fin 2, P.coeff n = b65e_residueJet p (Fin.castLE (by omega) n) q i j := by
  obtain ⟨P, hP, h0⟩ := b65e_residue_series_zero p O q i j
  refine ⟨P, hP, ?_⟩
  intro n
  fin_cases n
  · exact h0
  · exact b65e_residue_stored_coeff_one p O q i j hP

/-- Joint order-one agreement supplies the stored second coefficient at each fixed pole. -/
theorem b65e_fixed_residue_series_two (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (k : Fin 4) (i j : Fin 4) :
    ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ (.inl k) i j) P 0 ∧
      ∀ n : Fin 3, P.coeff n = (b65e_fixedJet (Fin.castLE (by omega) n) k i j : ℂ) := by
  have han : ∀ q i j, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 := by
    intro q i j
    exact b65q_MatAn.res O q i j 0 (Metric.mem_ball_self O.radius_pos)
  choose P hP using han
  have hc : ∀ a ≤ (0 : Fin 6).val + 1, ∀ q i j,
      (P q i j).coeff a = b65e_storedResidue p a q i j := by
    intro a ha q i j
    change a ≤ 1 at ha
    interval_cases a
    · change (P q i j).coeff 0 = b65e_residueJet p 0 q i j
      rw [b65e_residue_zero p O q]
      exact (hP q i j).coeff_zero _
    · exact b65e_residue_stored_coeff_one p O q i j (hP q i j)
  refine ⟨P (.inl k) i j, hP _ _ _, ?_⟩
  intro n
  fin_cases n
  · exact hc 0 (by decide) (.inl k) i j
  · exact hc 1 (by decide) (.inl k) i j
  · exact b65e_fixed_coeff_next p O hP 0 hc k i j

/-- The same analytic series realizes the first two stored coefficients at each fixed pole. -/
theorem b65e_fixed_residue_series_one (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (k : Fin 4) (i j : Fin 4) :
    ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ (Sum.inl k) i j) P 0 ∧
      P.coeff 0 = (b65e_fixedJet 0 k i j : ℂ) ∧
      P.coeff 1 = (b65e_fixedJet 1 k i j : ℂ) := by
  obtain ⟨P, hP, h0⟩ := b65e_residue_series_zero p O (Sum.inl k) i j
  exact ⟨P, hP, h0, b65e_fixed_residue_coeff_one p O k i j hP⟩

/-- Moving-pole field steps, together with the checked fixed fields, determine
all eight coefficients of the analytic residue series. -/
theorem b65e_residue_jet_of_moving_steps (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hmov : ∀ n < 7, ∀ x : Fin 12, ∀ i j : Fin 4,
      b65e_fieldCoeff p (b65e_storedResidue p) n (.inr x) i j =
        (n + 1 : ℂ) * b65e_storedResidue p (n + 1) (.inr x) i j) :
    ∀ q : Fin 4 ⊕ Fin 12, ∀ i j : Fin 4, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = b65e_residueJet p n q i j := by
  have han : ∀ q i j, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 := by
    intro q i j
    exact b65q_MatAn.res O q i j 0 (Metric.mem_ball_self O.radius_pos)
  choose P hP using han
  have hz (q i j) : (P q i j).coeff 0 = b65e_storedResidue p 0 q i j := by
    change (P q i j).coeff 0 = b65e_residueJet p 0 q i j
    rw [b65e_residue_zero p O q]
    exact (hP q i j).coeff_zero _
  have hbase : b65e_storedResidue p 0 = fun q ↦ b65q_mat (b65p_initialResidue q) := by
    funext q i j
    rw [← hz q i j]
    calc
      (P q i j).coeff 0 = b65q_res O.residue 0 q i j := (hP q i j).coeff_zero _
      _ = _ := by simp only [b65q_res, O.residue_zero]
  have hstep : ∀ n : ℕ, n < 7 → ∀ q i j,
      (n + 1 : ℂ) * b65e_storedResidue p (n + 1) q i j =
        b65e_fieldCoeff p (b65e_storedResidue p) n q i j := by
    intro n hn q i j
    cases q with
    | inl k =>
      interval_cases n
      · have hr := b65e_residue_coeff_recurrence p O hP 0 (.inl k) i j
        have hc : ∀ a ≤ 0,
            (fun q i j ↦ (P q i j).coeff a) = b65e_storedResidue p a := by
          intro a ha
          have : a = 0 := by omega
          subst a
          funext q i j
          exact hz q i j
        rw [b65e_fieldCoeff_congr p 0 hc,
          b65e_fixed_residue_coeff_one p O k i j (hP (.inl k) i j)] at hr
        exact hr
      · convert (b65e_fixed_stored_step p O 0 k i j).symm using 1 <;>
          norm_num [b65e_storedResidue, b65e_residueJet]
      · convert (b65e_fixed_stored_step p O 1 k i j).symm using 1 <;>
          norm_num [b65e_storedResidue, b65e_residueJet]
      · convert (b65e_fixed_stored_step p O 2 k i j).symm using 1 <;>
          norm_num [b65e_storedResidue, b65e_residueJet]
      · convert (b65e_fixed_stored_step p O 3 k i j).symm using 1 <;>
          norm_num [b65e_storedResidue, b65e_residueJet]
      · convert (b65e_fixed_stored_step p O 4 k i j).symm using 1 <;>
          norm_num [b65e_storedResidue, b65e_residueJet]
      · convert (b65e_fixed_stored_step p O 5 k i j).symm using 1 <;>
          norm_num [b65e_storedResidue, b65e_residueJet]
    | inr x =>
      exact (hmov n hn x i j).symm
  have hall := b65e_residue_coeff_of_recurrence p O (b65e_storedResidue p) 7
    hbase hstep hP
  intro q i j
  refine ⟨P q i j, hP q i j, ?_⟩
  intro n
  have h := hall n.val (by omega) q i j
  have hn : Fin.ofNat 8 n.val = n := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt n.isLt
  simpa only [b65e_storedResidue, hn] using h

/-- Rational moving-field remainders, together with the checked fixed fields, determine
all eight coefficients of the analytic residue series. -/
theorem b65e_residue_jet_of_moving_remainders (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hrem : ∀ n : Fin 7, ∀ e : Fin 2, ∀ i j : Fin 4,
      (b65e_reducedMovingFieldQ b65e_storedFixedQ b65e_storedMovingQ n e i j) %ₘ
          b65e_fibrePolynomialQ e =
        C (n.val + 1 : ℚ) * b65e_storedMovingQ (n.val + 1) e i j) :
    ∀ q : Fin 4 ⊕ Fin 12, ∀ i j : Fin 4, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = b65e_residueJet p n q i j :=
  b65e_residue_jet_of_moving_steps p O fun n hn x i j ↦
    b65e_moving_stored_step_of_remainder p O n x i j (hrem ⟨n, hn⟩ (b65q_fibreIndex x) i j)

/-- The analytic residues have the stored Taylor coefficients through order seven. -/
theorem b65e_residue_jet_series (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ q : Fin 4 ⊕ Fin 12, ∀ i j : Fin 4, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = b65e_residueJet p n q i j :=
  b65e_residue_jet_of_moving_steps p O fun n hn x i j ↦
    b65e_moving_stored_step p O ⟨n, hn⟩ x i j

end HodgeLean.Foundations.Program
