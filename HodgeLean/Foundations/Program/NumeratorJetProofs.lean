import HodgeLean.Foundations.Program.NumeratorJetResidueJet
import HodgeLean.Foundations.Program.NumeratorJetNumeratorJet
import HodgeLean.Foundations.Program.NumeratorJetQFrameEvaluation
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

/-! # B6-5 stage 5e: auxiliary statements (open bodies)

One auxiliary per public statement of `NumeratorJet.lean`, with the same signature.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b65e_residue_jet_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ q : Fin 4 ⊕ Fin 12, ∀ i j : Fin 4, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ q i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = b65e_residueJet p n q i j :=
  b65e_residue_jet_series p O

theorem b65e_rFrameJet_zero_table : b65e_rFrameJet 0 = b65k_rKernel := by
  rw [b65k_rKernel_eq]
  decide +kernel

theorem b65e_qFrameJet_zero_table : b65e_qFrameJet 0 = b65k_qKernel := by
  rw [b65k_qKernel_eq]
  decide +kernel

theorem b65e_frame_series_zero (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    (∀ i : Fin 36, ∀ f : Fin 3, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_rFrame p O.residue θ i f) P 0 ∧
        P.coeff 0 = (b65e_rFrameJet 0 i f : ℂ)) ∧
    ∀ i : Fin 48, ∀ f : Fin 3, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_qFrame p O.residue θ i f) P 0 ∧
        P.coeff 0 = (b65e_qFrameJet 0 i f : ℂ) := by
  obtain ⟨ε, hε, _, hr, hq, _, hr0, hq0, _⟩ := b65q_frames p O
  constructor
  · intro i f
    obtain ⟨P, hP⟩ := hr i f 0 (Metric.mem_ball_self hε)
    refine ⟨P, hP, ?_⟩
    rw [b65e_rFrameJet_zero_table]
    change P 0 (fun _ ↦ 1) = _
    calc
      _ = b65q_rFrame p O.residue 0 i f := hP.coeff_zero _
      _ = _ := by rw [hr0]; rfl
  · intro i f
    obtain ⟨P, hP⟩ := hq i f 0 (Metric.mem_ball_self hε)
    refine ⟨P, hP, ?_⟩
    rw [b65e_qFrameJet_zero_table]
    change P 0 (fun _ ↦ 1) = _
    calc
      _ = b65q_qFrame p O.residue 0 i f := hP.coeff_zero _
      _ = _ := by rw [hq0]; rfl

theorem b65e_frame_jet_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    (∀ i : Fin 36, ∀ f : Fin 3, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_rFrame p O.residue θ i f) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_rFrameJet n i f : ℂ)) ∧
    ∀ i : Fin 48, ∀ f : Fin 3, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65q_qFrame p O.residue θ i f) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_qFrameJet n i f : ℂ) := by
  obtain ⟨ε, hε, -, hr, hq, -⟩ := b65q_frames p O
  have hn8 (n : Fin 8) : (Fin.ofNat 8 n.val : Fin 8) = n := Fin.ext (by simp)
  constructor
  · intro i f
    obtain ⟨P, hP⟩ := hr i f 0 (Metric.mem_ball_self hε)
    refine ⟨P, hP, fun n ↦ ?_⟩
    rw [← b65e_T_coeff_of_series hP]
    have h := congrFun (congrFun (b65e_rFrame_TC p O n n.isLt) i) f
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65e_rFrameN, Rat.coe_castHom,
      hn8] at h
    exact h
  · intro i f
    obtain ⟨P, hP⟩ := hq i f 0 (Metric.mem_ball_self hε)
    refine ⟨P, hP, fun n ↦ ?_⟩
    rw [← b65e_T_coeff_of_series hP]
    have h := congrFun (congrFun (b65e_qFrame_TC p O n n.isLt) i) f
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65e_qFrameN, Rat.coe_castHom,
      hn8] at h
    exact h

theorem b65e_coupling_disc (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      ∀ θ ∈ ball (0 : ℂ) ε,
        b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 →
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 →
        b65e_numerator p O.residue θ = b65q_numMatrix p O.residue θ := by
  obtain ⟨ε, hε, hεr, hpoly, _⟩ := b65q_family_numerators p O
  refine ⟨ε, hε, hεr, ?_⟩
  intro θ hθ hr hq
  have hd : ∀ a b, (b65q_frameProduct p O.residue θ a b).denom = 1 := by
    intro a b
    exact (hpoly θ hθ _ _ (b65q_col_ker _ _ hr a) (b65q_col_ker _ _ hq b)).1
  ext i j
  simp only [b65e_numerator, b65q_numMatrix, b65e_polyPart, hd,
    Polynomial.divByMonic_one]

theorem b65e_numerator_zero (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    b65e_numerator p O.residue 0 = b65k_baseMatrix.map (Rat.castHom ℂ) := by
  have hd : ∀ a b, (b65q_frameProduct p O.residue 0 a b).denom = 1 := by
    intro a b
    rw [b65q_frameProduct_zero O]
    have hbase := (b65k_base_numerator a b).1
    have hb : b65k_baseProduct a b =
        algebraMap ℚ[X] (RatFunc ℚ) (b65k_baseProduct a b).num := by
      nth_rw 1 [← RatFunc.num_div_denom (b65k_baseProduct a b)]
      rw [hbase, map_one, div_one]
    rw [hb, b65q_castRat_algebraMap, RatFunc.denom_algebraMap]
  calc
    b65e_numerator p O.residue 0 = b65q_numMatrix p O.residue 0 := by
      ext i j
      simp only [b65e_numerator, b65q_numMatrix, b65e_polyPart, hd,
        Polynomial.divByMonic_one]
    _ = _ := b65q_numMatrix_zero O

theorem b65e_numerator_analytic_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ i : Fin 9, ∀ j : Fin 10,
        AnalyticOnNhd ℂ (fun θ ↦ b65e_numerator p O.residue θ i j) (ball 0 ε)) ∧
      (∀ θ ∈ ball (0 : ℂ) ε,
        b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 →
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 →
        b65e_numerator p O.residue θ = b65q_numMatrix p O.residue θ) ∧
      b65e_numerator p O.residue 0 = b65k_baseMatrix.map (Rat.castHom ℂ) := by
  obtain ⟨r, hr, hrr, han⟩ := b65e_entries_analytic p O
  obtain ⟨t, ht, _, hc⟩ := b65e_coupling_disc p O
  refine ⟨min r t, lt_min hr ht, (min_le_left r t).trans hrr, ?_, ?_,
    b65e_numerator_zero p O⟩
  · exact fun i j ↦ (han i j).mono (ball_subset_ball (min_le_left r t))
  · exact fun θ hθ ↦ hc θ (ball_subset_ball (min_le_right r t) hθ)

theorem b65e_numerator_jet_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ i : Fin 9, ∀ j : Fin 10, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65e_numerator p O.residue θ i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_N n i j : ℂ) :=
  b65e_numerator_jet_series p O

theorem b65e_jet_eq_export_aux :
    ∀ n : Fin 8, ∀ i : Fin 9, ∀ j : Fin 10,
      b65e_N n i j = PowerSeries.coeff (n : ℕ) (papers8_Mseries i j) := by
  intro n i j
  simp only [papers8_Mseries, map_sum, PowerSeries.coeff_monomial]
  rw [Finset.sum_eq_single n]
  · fin_cases n <;> fin_cases i <;> fin_cases j <;> decide +kernel
  · intro b _ h
    simp only [ite_eq_right (show n.val ≠ b.val from fun hv ↦ h (Fin.ext hv.symm))]
  · simp

theorem b65e_certified_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    g32r_CertifiedJet (b65e_numerator p O.residue) := by
  choose P hP hcoeff using b65e_numerator_jet_aux p O
  refine ⟨P, hP, ?_⟩
  intro i j k hk
  let n : Fin 8 := ⟨k, by omega⟩
  rw [hcoeff i j n, b65e_jet_eq_export_aux n i j]
  rfl

theorem b65e_certified_numMatrix_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    (∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0) →
      b65q_numMatrix p O.residue =ᶠ[𝓝 0] b65e_numerator p O.residue ∧
        g32r_CertifiedJet (b65q_numMatrix p O.residue) := by
  intro hk
  obtain ⟨ε, hε, _, hc⟩ := b65e_coupling_disc p O
  have heq : b65q_numMatrix p O.residue =ᶠ[𝓝 0] b65e_numerator p O.residue := by
    filter_upwards [hk, Metric.ball_mem_nhds (0 : ℂ) hε] with θ hθ hball
    exact (hc θ hball hθ.1 hθ.2).symm
  refine ⟨heq, ?_⟩
  obtain ⟨P, hP, hcoeff⟩ := b65e_certified_aux p O
  refine ⟨P, ?_, hcoeff⟩
  intro i j
  exact (hP i j).congr (heq.symm.mono fun θ hθ ↦ congrFun (congrFun hθ i) j)

end HodgeLean.Foundations.Program
