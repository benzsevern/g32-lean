import HodgeLean.Foundations.Program.NumeratorJetRFrameCertificates
import HodgeLean.Foundations.Program.KernelFramesFamily
import HodgeLean.Foundations.Program.KernelFramesCert

/-! # Taylor coefficients of the r-frame along the path -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "ι" => Rat.castHom ℂ

/-- Convolution solutions with prescribed free rows and invertible pivot block are unique. -/
theorem b65e_frame_unique {q n : ℕ} (L : ℕ → Matrix (Fin q) (Fin n) ℂ) (piv : Fin q → Fin n)
    (free : Fin 3 → Fin n) (hbij : Function.Bijective (Sum.elim piv free))
    (C : Matrix (Fin q) (Fin q) ℂ) (hC : C * (L 0).submatrix id piv = 1)
    (X Y : ℕ → Matrix (Fin n) (Fin 3) ℂ) (N : ℕ)
    (hX : ∀ k < N, ∑ a ∈ Finset.range (k + 1), L a * X (k - a) = 0)
    (hY : ∀ k < N, ∑ a ∈ Finset.range (k + 1), L a * Y (k - a) = 0)
    (hfree : ∀ k < N, ∀ a f, X k (free a) f = Y k (free a) f) :
    ∀ k < N, X k = Y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hx := hX k hk
    have hy := hY k hk
    rw [Finset.sum_range_succ'] at hx hy
    have hs : ∑ a ∈ Finset.range k, L (a + 1) * X (k - (a + 1)) =
        ∑ a ∈ Finset.range k, L (a + 1) * Y (k - (a + 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have := Finset.mem_range.mp ha
      rw [ih (k - (a + 1)) (by omega) (by omega)]
    simp only [Nat.sub_zero] at hx hy
    have hD : L 0 * (X k - Y k) = 0 := by
      rw [Matrix.mul_sub]
      have : L 0 * X k = L 0 * Y k := by
        rw [← add_left_cancel_iff (a := ∑ a ∈ Finset.range k, L (a + 1) * X (k - (a + 1))),
          hx]
        rw [hs, hy]
      rw [this, sub_self]
    set D := X k - Y k with hDdef
    have hDf : ∀ a f, D (free a) f = 0 := fun a f ↦ by
      rw [hDdef, Matrix.sub_apply, hfree k hk a f, sub_self]
    have hP : (L 0).submatrix id piv * D.submatrix piv id = 0 := by
      ext r f
      have h := congrFun (congrFun hD r) f
      rw [Matrix.mul_apply, b65q_sum_split piv free hbij] at h
      simp only [hDf, mul_zero, Finset.sum_const_zero, add_zero] at h
      rw [Matrix.mul_apply]
      simpa using h
    have hP' : D.submatrix piv id = 0 := by
      rw [← Matrix.one_mul (D.submatrix piv id), ← hC, Matrix.mul_assoc, hP, Matrix.mul_zero]
    have hz : D = 0 := by
      ext i f
      obtain ⟨s, hs⟩ := hbij.2 i
      rcases s with b | a
      · simp only [Sum.elim_inl] at hs
        rw [← hs]
        exact congrFun (congrFun hP' b) f
      · simp only [Sum.elim_inr] at hs
        rw [← hs]
        exact hDf a f
    exact sub_eq_zero.mp hz

set_option maxHeartbeats 400000 in
/-- The rational block inverse inverts the order-zero selected pivot block. -/
theorem b65e_rBlockInv_mul : b65k_rBlockInv *
    (b65e_rSystemJetQ 0).submatrix b65k_rRows b65k_rPivot = 1 := by
  decide +kernel

/-- The kernel checks assembled over the orders. -/
theorem b65e_rFrameJet_kernel (n : ℕ) (hn : n < 8) :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN n = 0 := by
  interval_cases n
  · exact b65e_rFrameJet_kernel_0
  · exact b65e_rFrameJet_kernel_1
  · exact b65e_rFrameJet_kernel_2
  · exact b65e_rFrameJet_kernel_3
  · exact b65e_rFrameJet_kernel_4
  · exact b65e_rFrameJet_kernel_5
  · exact b65e_rFrameJet_kernel_6
  · exact b65e_rFrameJet_kernel_7

/-- The r-frame along the path has the stored Taylor coefficients through order seven. -/
theorem b65e_rFrame_TC (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∀ n < 8, b65e_TC (fun θ ↦ b65q_rFrame p O.residue θ) n = (b65e_rFrameN n).map ι := by
  obtain ⟨ε, hε, -, hk⟩ := b65q_frames_kernel p O
  obtain ⟨ε', hε', -, hr, -⟩ := b65q_frames p O
  obtain ⟨ε₀, hε₀, hε₀r, hgood⟩ := b65q_good_disc O
  have hfam := (b65q_family_an O hε₀r hgood).1
  have hFa : ∀ i j, AnalyticAt ℂ (fun θ ↦ (b65q_rFamily p O.residue θ).submatrix b65k_rRows id i j)
      0 := fun i j ↦ hfam _ j 0 (mem_ball_self hε₀)
  have hRa : ∀ i f, AnalyticAt ℂ (fun θ ↦ b65q_rFrame p O.residue θ i f) 0 :=
    fun i f ↦ hr i f 0 (mem_ball_self hε')
  have hL : ∀ a < 8, b65e_TC (fun θ ↦ (b65q_rFamily p O.residue θ).submatrix b65k_rRows id) a =
      ((b65e_rSystemJetQ a).submatrix b65k_rRows id).map ι := by
    intro a ha
    rw [b65e_TC_submatrix, b65e_rFamily_TC p O a ha]
    rfl
  intro n hn
  refine b65e_frame_unique
    (fun a ↦ b65e_TC (fun θ ↦ (b65q_rFamily p O.residue θ).submatrix b65k_rRows id) a)
    b65k_rPivot b65k_rFree b65k_r_bijective (b65k_rBlockInv.map ι) ?_ _
    (fun a ↦ (b65e_rFrameN a).map ι) 8 ?_ ?_ ?_ n hn
  · rw [hL 0 (by omega), ← Matrix.submatrix_map, Matrix.submatrix_submatrix]
    simp only [Function.comp_id, Function.id_comp]
    rw [Matrix.submatrix_map, ← Matrix.map_mul, b65e_rBlockInv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro k hk'
    rw [← b65e_TC_mul hFa hRa, b65e_TC_congr (G := fun _ ↦ 0) (by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with θ hθ
      exact (hk θ hθ).1), b65e_TC_const]
    split_ifs <;> rfl
  · intro k hk'
    rw [Finset.sum_congr rfl fun a ha ↦ by
      rw [hL a (by have := Finset.mem_range.mp ha; omega)]]
    rw [← b65e_map_convQ, b65e_rFrameJet_kernel k hk']
    simp
  · intro k hk' a f
    have hc : (fun θ ↦ b65q_rFrame p O.residue θ (b65k_rFree a) f) =
        fun _ ↦ if a = f then (1 : ℂ) else 0 := by
      funext θ
      rw [b65q_rFrame_eq, b65q_ibFrame_free _ _ _ _ b65k_r_bijective]
    have hkv : ((Fin.ofNat 8 k : Fin 8) : ℕ) = k := by simp [Nat.mod_eq_of_lt hk']
    simp only [b65e_TC, Matrix.of_apply, Matrix.map_apply, b65e_rFrameN]
    rw [hc, b65q_T_const, PowerSeries.coeff_C, b65e_rFrameJet_free, hkv]
    by_cases h0 : k = 0 <;> by_cases haf : a = f <;> simp [h0, haf]

end HodgeLean.Foundations.Program
