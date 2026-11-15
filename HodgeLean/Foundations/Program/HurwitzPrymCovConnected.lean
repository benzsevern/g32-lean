import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: a surface minus finitely many points is connected

A punctured ball in a real normed space of dimension at least two is connected (the image of a
sphere times an interval). Every point of a Riemann surface has arbitrarily small open
neighborhoods whose punctured version is connected, and removing such a point from an open
preconnected set keeps it preconnected; so removing a finite set does too.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology Metric
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Punctured

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A punctured ball is connected** in dimension at least two. -/
theorem b4cov_isConnected_ball_diff (h : 1 < Module.rank ℝ F) (x : F) {r : ℝ} (hr : 0 < r) :
    IsConnected (ball x r \ {x}) := by
  have hS := (isConnected_sphere h (0 : F) zero_le_one).prod (isConnected_Ioo hr)
  have hcont : Continuous fun p : F × ℝ ↦ x + p.2 • p.1 := by fun_prop
  convert hS.image _ hcont.continuousOn using 1
  ext y
  constructor
  · rintro ⟨hy, hyx⟩
    have hne : y - x ≠ 0 := sub_ne_zero.2 hyx
    have hn : 0 < ‖y - x‖ := norm_pos_iff.2 hne
    refine ⟨(‖y - x‖⁻¹ • (y - x), ‖y - x‖), ⟨?_, hn, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · rwa [mem_ball, dist_eq_norm] at hy
    · simp only [smul_smul, mul_inv_cancel₀ hn.ne', one_smul, add_sub_cancel]
  · rintro ⟨⟨v, t⟩, ⟨hv, ht0, htr⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hv
    refine ⟨?_, fun h0 ↦ ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
        Real.norm_of_nonneg ht0.le]
      exact htr
    · have : t • v = 0 := by simpa using h0
      rcases smul_eq_zero.1 this with h1 | h1
      · exact ht0.ne' h1
      · rw [h1, norm_zero] at hv; exact zero_ne_one hv

end Punctured

section Remove

variable {X : Type*} [TopologicalSpace X] [T1Space X]

/-- Points with arbitrarily small open neighborhoods whose punctured version is preconnected and
nonempty. -/
def b4cov_GoodPoint (s : X) : Prop :=
  ∀ N ∈ 𝓝 s, ∃ U ⊆ N, IsOpen U ∧ s ∈ U ∧ IsPreconnected (U \ {s}) ∧ (U \ {s}).Nonempty

/-- **Removing a good point keeps an open preconnected set preconnected.** -/
theorem b4cov_isPreconnected_diff_singleton {W : Set X} (hWo : IsOpen W) (hW : IsPreconnected W)
    {s : X} (hs : b4cov_GoodPoint s) : IsPreconnected (W \ {s}) := by
  by_cases hsW : s ∉ W
  · rwa [diff_singleton_eq_self hsW]
  rw [not_not] at hsW
  obtain ⟨U, hUW, hUo, hsU, hUc, hUne⟩ := hs W (hWo.mem_nhds hsW)
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  have hUcov : U \ {s} ⊆ u ∪ v := fun z hz ↦ hcov ⟨hUW hz.1, hz.2⟩
  have hUdisj : U \ {s} ∩ (u ∩ v) = ∅ := by
    refine eq_empty_of_forall_notMem fun z ⟨hz, hzuv⟩ ↦ ?_
    have : z ∈ W \ {s} ∩ (u ∩ v) := ⟨⟨hUW hz.1, hz.2⟩, hzuv⟩
    rw [hdisj] at this; exact this
  have hUsub := (isPreconnected_iff_subset_of_disjoint.1 hUc) u v hu hv hUcov hUdisj
  -- the side containing the punctured neighborhood absorbs `s`
  have key : ∀ {u v : Set X}, IsOpen u → IsOpen v → W \ {s} ⊆ u ∪ v →
      W \ {s} ∩ (u ∩ v) = ∅ → U \ {s} ⊆ u → W \ {s} ⊆ u := by
    intro u v hu hv hcov hdisj hUu
    have hcov' : W ⊆ (u ∪ U) ∪ (v \ {s}) := by
      intro w hw
      by_cases hws : w = s
      · exact Or.inl (Or.inr (hws ▸ hsU))
      · rcases hcov ⟨hw, hws⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hws⟩
    have hdisj' : W ∩ ((u ∪ U) ∩ (v \ {s})) = ∅ := by
      refine eq_empty_of_forall_notMem fun w ⟨hw, hwu, hwv, hws⟩ ↦ ?_
      have hwu' : w ∈ u := hwu.elim id fun h ↦ hUu ⟨h, hws⟩
      have : w ∈ W \ {s} ∩ (u ∩ v) := ⟨⟨hw, hws⟩, hwu', hwv⟩
      rw [hdisj] at this; exact this
    rcases (isPreconnected_iff_subset_of_disjoint.1 hW) _ _ (hu.union hUo)
        (hv.sdiff isClosed_singleton) hcov' hdisj' with h | h
    · intro w hw
      exact (h hw.1).elim id fun h' ↦ hUu ⟨h', hw.2⟩
    · exact absurd (h hsW).2 (by simp)
  rcases hUsub with h | h
  · exact Or.inl (key hu hv hcov hdisj h)
  · refine Or.inr (key hv hu (fun z hz ↦ (hcov hz).symm) ?_ h)
    rwa [inter_comm v u]

/-- **Removing finitely many good points keeps an open preconnected set preconnected.** -/
theorem b4cov_isPreconnected_diff_finite {W : Set X} (hWo : IsOpen W) (hW : IsPreconnected W)
    {S : Set X} (hS : S.Finite) (hgood : ∀ s ∈ S, b4cov_GoodPoint s) :
    IsPreconnected (W \ S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa using hW
  | @insert a S haS hS ih =>
    rw [insert_eq, union_comm, ← Set.sdiff_sdiff]
    exact b4cov_isPreconnected_diff_singleton (hWo.sdiff hS.isClosed)
      (ih fun s hs ↦ hgood s (mem_insert_of_mem a hs)) (hgood a (mem_insert a S))

end Remove

section Surface

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]

/-- **Every point of a Riemann surface is good**: punctured chart balls are connected. -/
theorem b4cov_goodPoint (hE : Module.finrank ℂ E = 1) (s : C) : b4cov_GoodPoint s := by
  have hrank : 1 < Module.rank ℝ E := by
    have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
    rw [← Module.finrank_eq_rank, finrank_real_of_complex, hE]
    norm_num
  intro N hN
  let φ := chartAt E s
  have hTo : IsOpen (φ.target ∩ φ.symm ⁻¹' interior N) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target isOpen_interior
  have hsT : φ s ∈ φ.target ∩ φ.symm ⁻¹' interior N := by
    refine ⟨φ.map_source (mem_chart_source E s), ?_⟩
    rw [mem_preimage, φ.left_inv (mem_chart_source E s)]
    exact mem_interior_iff_mem_nhds.2 hN
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 hTo _ hsT
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ s) r, ?_, φ.isOpen_inter_preimage isOpen_ball,
    ⟨mem_chart_source E s, mem_ball_self hr⟩, ?_⟩
  · rintro y ⟨hys, hyb⟩
    have := (hrT hyb).2
    rw [mem_preimage, φ.left_inv hys] at this
    exact interior_subset this
  have heq : (φ.source ∩ φ ⁻¹' ball (φ s) r) \ {s} = φ.symm '' (ball (φ s) r \ {φ s}) := by
    ext y
    constructor
    · rintro ⟨⟨hys, hyb⟩, hysne⟩
      refine ⟨φ y, ⟨hyb, fun h ↦ hysne ?_⟩, φ.left_inv hys⟩
      exact φ.injOn hys (mem_chart_source E s) h
    · rintro ⟨z, ⟨hzb, hzs⟩, rfl⟩
      have hzt : z ∈ φ.target := (hrT hzb).1
      refine ⟨⟨φ.map_target hzt, ?_⟩, fun h ↦ hzs ?_⟩
      · rw [mem_preimage, φ.right_inv hzt]; exact hzb
      · rw [← φ.right_inv hzt, Set.mem_singleton_iff.1 h]; rfl
  have hc := b4cov_isConnected_ball_diff hrank (φ s) hr
  rw [heq]
  refine ⟨hc.isPreconnected.image _ (φ.continuousOn_symm.mono fun z hz ↦ (hrT hz.1).1),
    hc.nonempty.image _⟩

end Surface

end HodgeLean.Foundations.Program
