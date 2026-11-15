import HodgeLean.Foundations.Program.NumeratorJetNumeratorTables
import HodgeLean.Foundations.Program.NumeratorJetNumeratorEvaluation
import HodgeLean.Foundations.Program.NumeratorJetQFrameEvaluation
import HodgeLean.Foundations.Program.NumeratorJetRFrameEvaluation
import HodgeLean.Foundations.Program.NumeratorJetLeftEvaluation
import HodgeLean.Foundations.Program.NumeratorJetAnalytic

/-! # The numerator jets

The frame and left-vector Taylor coefficients, together with the assembled table checks, give
the Taylor coefficients of every numerator entry through order seven.
-/

noncomputable section
open Set Metric
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Every numerator entry has the stored Taylor coefficients through order seven. -/
theorem b65e_numerator_jet_series (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ i : Fin 9, ∀ j : Fin 10, ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun θ ↦ b65e_numerator p O.residue θ i j) P 0 ∧
        ∀ n : Fin 8, P.coeff n = (b65e_N n i j : ℂ) := by
  obtain ⟨ε, hε, -, hr, hq, -⟩ := b65q_frames p O
  obtain ⟨t, ht, -, -, hw, -⟩ := b65q_normalizations p O
  obtain ⟨s, hs, -, han⟩ := b65e_entries_analytic p O
  have hra : ∀ i a, AnalyticAt ℂ (fun θ ↦ b65q_rFrame p O.residue θ i a) 0 :=
    fun i a ↦ hr i a 0 (mem_ball_self hε)
  have hqa : ∀ i b, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i b) 0 :=
    fun i b ↦ hq i b 0 (mem_ball_self hε)
  have hwa : ∀ x i, AnalyticAt ℂ (fun θ ↦ b65q_left O.residue θ x i) 0 :=
    fun x i ↦ hw x i 0 (mem_ball_self ht)
  have hrT : ∀ i a n, n < 8 →
      PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_rFrame p O.residue θ i a) 0) =
        (b65e_rFrameJet (Fin.ofNat 8 n) i a : ℂ) := by
    intro i a n hn
    have h := congrFun (congrFun (b65e_rFrame_TC p O n hn) i) a
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65e_rFrameN, Rat.coe_castHom] at h
    exact h
  have hqT : ∀ i b n, n < 8 →
      PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_qFrame p O.residue θ i b) 0) =
        (b65e_qFrameJet (Fin.ofNat 8 n) i b : ℂ) := by
    intro i b n hn
    have h := congrFun (congrFun (b65e_qFrame_TC p O n hn) i) b
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65e_qFrameN, Rat.coe_castHom] at h
    exact h
  have hwT : ∀ x i n, n < 8 →
      PowerSeries.coeff n (b65q_T (fun θ ↦ b65q_left O.residue θ x i) 0) =
        b65e_coordinateEvalQ (b65e_leftCoordsQ (b65q_fibreIndex x) i (Fin.ofNat 8 n)) (p x) :=
    fun x i n hn ↦ congrFun (b65e_left_T p O x n hn) i
  intro i j
  obtain ⟨P, hP⟩ := han i j 0 (mem_ball_self hs)
  refine ⟨P, hP, fun n ↦ ?_⟩
  rw [← b65e_T_coeff_of_series hP]
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective i
  rw [b65e_numerator_T p O hqa hwa hqT hwT hra hrT b65e_WT_table b65e_Sq_table b65e_G_table
    a b j n n.isLt, b65e_N_table n a b j]

end HodgeLean.Foundations.Program
