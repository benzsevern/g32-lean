import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology Set Metric
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
set_option maxHeartbeats 400000

theorem compact_chart_cover_avoiding_closed_set (P : ℝ → C) (hP : Continuous P) (hper : Function.Periodic P 1)
    (S : Set C) (hS : IsClosed S) (hav : ∀ t, P t ∉ S) :
    ∃ N : ℕ, 0 < N ∧ ∃ x : ℤ → C, ∃ r : ℤ → ℝ,
      (∀ k, closedBall (chartAt E (x k) (x k)) (r k) ⊆ (chartAt E (x k)).target ∧
        (chartAt E (x k)).symm '' closedBall (chartAt E (x k) (x k)) (r k) ⊆ Sᶜ) ∧
      (∀ k, x (k + N) = x k) ∧
      (∀ k, r (k + N) = r k) ∧
      (∀ k, ball (chartAt E (x k) (x k)) (r k) ⊆ (chartAt E (x k)).target) ∧
      ∀ k : ℤ, ∀ τ ∈ Icc (0 : ℝ) 1, P ((k + τ) / N) ∈ (chartAt E (x k)).source ∧
        chartAt E (x k) (P ((k + τ) / N)) ∈ ball (chartAt E (x k) (x k)) (r k) := by
  have hρ : ∀ y : ↥(Sᶜ), ∃ ρ > 0, closedBall (chartAt E y.val y.val) ρ ⊆
      (chartAt E y.val).target ∩ (chartAt E y.val).symm ⁻¹' Sᶜ := by
    intro y
    obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
      ((chartAt E y.val).continuousOn_symm.isOpen_inter_preimage
        (chartAt E y.val).open_target hS.isOpen_compl) _
      ⟨(chartAt E y.val).map_source (mem_chart_source E y.val), by
        change (chartAt E y.val).symm (chartAt E y.val y.val) ∈ Sᶜ
        rw [(chartAt E y.val).left_inv (mem_chart_source E y.val)]
        exact y.property⟩
    exact ⟨ρ / 2, half_pos hρ,
      (closedBall_subset_ball (half_lt_self hρ)).trans hsub⟩
  choose ρ hρ0 hρ using hρ
  let U : ↥(Sᶜ) → Set C := fun y ↦
    (chartAt E y.val).source ∩ (chartAt E y.val) ⁻¹' ball (chartAt E y.val y.val) (ρ y)
  have hUo : ∀ y, IsOpen (P ⁻¹' U y) := fun y ↦
    ((chartAt E y.val).continuousOn.isOpen_inter_preimage (chartAt E y.val).open_source
      isOpen_ball).preimage hP
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ y, P ⁻¹' U y := fun t _ ↦
    mem_iUnion.2 ⟨⟨P t, hav t⟩, mem_chart_source E _, by simp [hρ0]⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hUo hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by positivity
  have hNz : (0 : ℤ) < N := by positivity
  have hsel : ∀ m : ℤ, ∃ y : ↥(Sᶜ), ball ((m % (N : ℤ) : ℤ) / (N : ℝ)) δ ⊆ P ⁻¹' U y := by
    intro m
    apply hball
    have h0 : (0 : ℝ) ≤ ((m % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg m hNz.ne'
    have h1 : ((m % (N : ℤ) : ℤ) : ℝ) < N := by exact_mod_cast Int.emod_lt_of_pos m hNz
    exact ⟨div_nonneg h0 hNpos.le, (div_le_one hNpos).2 h1.le⟩
  choose y hy using hsel
  refine ⟨N, Nat.succ_pos n, fun k ↦ (y (k % (N : ℤ))).val, fun k ↦ ρ (y (k % (N : ℤ))), ?_, ?_, ?_,
    fun k u hu ↦ (hρ _ (ball_subset_closedBall hu)).1, ?_⟩
  · intro k
    refine ⟨fun u hu => (hρ _ hu).1, ?_⟩
    rintro z ⟨u, hu, rfl⟩
    exact (hρ _ hu).2
  · intro k; simp only [Int.add_emod_right]
  · intro k; simp only [Int.add_emod_right]
  · intro k τ hτ
    set m := k % (N : ℤ)
    set q := k / (N : ℤ)
    have hk : (k : ℝ) = N * q + m := by exact_mod_cast (Int.mul_ediv_add_emod k N).symm
    have hPe : P ((k + τ) / N) = P ((m + τ) / N) := by
      have : (k + τ) / N = (m + τ) / N + (q : ℝ) * 1 := by
        rw [hk]; field_simp; ring
      rw [this]
      exact (hper.int_mul q) _
    have hmem : (m + τ) / (N : ℝ) ∈ ball ((m : ℝ) / N) δ := by
      rw [mem_ball, Real.dist_eq, add_div, add_sub_cancel_left, abs_of_nonneg
        (div_nonneg hτ.1 hNpos.le)]
      calc τ / N ≤ 1 / N := div_le_div_of_nonneg_right hτ.2 hNpos.le
        _ = 1 / ((n : ℝ) + 1) := by rw [hNdef]; push_cast; ring
        _ < δ := hn
    have hc : m % (N : ℤ) = m := Int.emod_emod _ _
    have := hy m (by rw [hc]; exact hmem)
    rw [hPe]
    exact this

end HodgeLean.Foundations.Curves.AbelTheorem
