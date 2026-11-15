import HodgeLean.Foundations.Program.NumeratorJetQSystemEvaluation
import HodgeLean.Foundations.Program.NumeratorJetQFrameCertificates
import HodgeLean.Foundations.Program.NumeratorJetRFrameEvaluation

/-! # Taylor coefficients of the q-frame along the path -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- The q-frame kernel checks assembled over the orders. -/
theorem b65e_qFrameJet_kernel (n : ℕ) (hn : n < 8) :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN n = 0 := by
  interval_cases n
  · exact b65e_qFrameJet_kernel_0
  · exact b65e_qFrameJet_kernel_1
  · exact b65e_qFrameJet_kernel_2
  · exact b65e_qFrameJet_kernel_3
  · exact b65e_qFrameJet_kernel_4
  · exact b65e_qFrameJet_kernel_5
  · exact b65e_qFrameJet_kernel_6
  · exact b65e_qFrameJet_kernel_7

/-- The q-frame along the path has the stored Taylor coefficients through order seven. -/
theorem b65e_qFrame_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_qFrame p O.residue θ) n = (b65e_qFrameN n).map ι := by
  obtain ⟨ε, hε, -, hk⟩ := b65q_frames_kernel p O
  obtain ⟨ε', hε', -, -, hq, -⟩ := b65q_frames p O
  obtain ⟨ε₀, hε₀, hε₀r, hgood⟩ := b65q_good_disc O
  have hfam := (b65q_family_an O hε₀r hgood).2
  have hFa : ∀ i j, AnalyticAt ℂ (fun θ ↦ (b65q_qFamily p O.residue θ).submatrix b65k_qRows id i j)
      0 := fun i j ↦ hfam _ j 0 (mem_ball_self hε₀)
  have hRa : ∀ i f, AnalyticAt ℂ (fun θ ↦ b65q_qFrame p O.residue θ i f) 0 :=
    fun i f ↦ hq i f 0 (mem_ball_self hε')
  have hL : ∀ a < 8, b65e_TC (fun θ ↦ (b65q_qFamily p O.residue θ).submatrix b65k_qRows id) a =
      ((b65e_qSystemJetQ a).submatrix b65k_qRows id).map ι := by
    intro a ha
    rw [b65e_TC_submatrix, b65e_qFamily_TC p O a ha]
    rfl
  intro n hn
  refine b65e_frame_unique
    (fun a ↦ b65e_TC (fun θ ↦ (b65q_qFamily p O.residue θ).submatrix b65k_qRows id) a)
    b65k_qPivot b65k_qFree b65k_q_bijective (b65k_qBlockInv.map ι) ?_ _
    (fun a ↦ (b65e_qFrameN a).map ι) 8 ?_ ?_ ?_ n hn
  · rw [hL 0 (by omega), ← Matrix.submatrix_map, Matrix.submatrix_submatrix]
    simp only [Function.comp_id, Function.id_comp]
    rw [Matrix.submatrix_map, ← Matrix.map_mul, b65e_qBlockInv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · intro k hk'
    rw [← b65e_TC_mul hFa hRa, b65e_TC_congr (G := fun _ ↦ 0) (by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with θ hθ
      exact (hk θ hθ).2.1), b65e_TC_const]
    split_ifs <;> rfl
  · intro k hk'
    rw [Finset.sum_congr rfl fun a ha ↦ by
      rw [hL a (by have := Finset.mem_range.mp ha; omega)]]
    rw [← b65e_map_convQ, b65e_qFrameJet_kernel k hk']
    simp
  · intro k hk' a f
    have hc : (fun θ ↦ b65q_qFrame p O.residue θ (b65k_qFree a) f) =
        fun _ ↦ if a = f then (1 : ℂ) else 0 := by
      funext θ
      rw [b65q_qFrame_eq, b65q_ibFrame_free _ _ _ _ b65k_q_bijective]
    have hkv : ((Fin.ofNat 8 k : Fin 8) : ℕ) = k := by simp [Nat.mod_eq_of_lt hk']
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65e_qFrameN]
    rw [hc, b65q_T_const, PowerSeries.coeff_C, b65e_qFrameJet_free, hkv]
    by_cases h0 : k = 0 <;> by_cases haf : a = f <;> simp [h0, haf]

end HodgeLean.Foundations.Program
