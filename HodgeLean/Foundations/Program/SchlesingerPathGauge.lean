import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsTransport

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_segment_gauge (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A B G : ℂ → E →L[ℂ] E) (a b : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r))
    (hB : AnalyticOnNhd ℂ B (ball a r))
    (hG : ∀ z ∈ ball a r, HasDerivAt G (B z * G z - G z * A z) z)
    (hb : b ∈ ball a r) :
    b65f_segment E B a b * G a = G b * b65f_segment E A a b := by
  have hd (z : ℂ) (hz : z ∈ ball a r) :
      HasDerivAt (fun w ↦ G w * b65f_segment E A a w)
        (B z * (G z * b65f_segment E A a z)) z := by
    convert (hG z hz).mul (b65f_segment_hasDerivAt hA hz) using 1
    noncomm_ring
  simpa only [b65f_segment_initial, mul_one] using
    b65f_segment_propagates hr hB hd hb

theorem b65p_transport_gauge (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (A B G : ℂ → E →L[ℂ] E) (U : Set ℂ)
    (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hG : ∀ z ∈ U, HasDerivAt G (B z * G z - G z * A z) z)
    (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1))
    (hm : MapsTo γ (Icc 0 1) U) :
    b65f_transport E B γ * G (γ 0) = G (γ 1) * b65f_transport E A γ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.image_of_continuousOn hc).exists_thickening_subset_open
    hU (image_subset_iff.mpr hm)
  obtain ⟨N, hN⟩ := b65t_dyadic_near γ hc hδ
  have he : ∀ᶠ n in atTop, b65f_polygon E B γ n * G (γ 0) =
      G (γ 1) * b65f_polygon E A γ n := by
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
    let k := 2 ^ n
    have hk : (k : ℝ) = (2 : ℝ) ^ n := by simp [k]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hstep (i : ℕ) (hi : i < k) :
        b65f_segment E B (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k)) *
          G (γ ((i : ℝ) / k)) =
        G (γ (((i : ℝ) + 1) / k)) *
          b65f_segment E A (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k)) := by
      obtain ⟨ht, hd⟩ := hN n hn i hi
      have hball : ball (γ ((i : ℝ) / k)) δ ⊆ U := by
        rw [hk]
        exact (ball_subset_thickening (mem_image_of_mem γ ht) δ).trans hsub
      apply b65p_segment_gauge E A B G _ _ δ hδ (hA.mono hball) (hB.mono hball)
        (fun z hz ↦ hG z (hball hz))
      simpa only [hk, mem_ball] using hd
    have hp := b65f_reverseProduct_intertwines
      (fun i ↦ b65f_segment E B (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k)))
      (fun i ↦ b65f_segment E A (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k)))
      (fun i ↦ G (γ ((i : ℝ) / k))) k (by
        intro i hi
        simpa only [Nat.cast_add, Nat.cast_one] using hstep i hi)
    simpa [b65f_polygon, b65f_reverseProduct, hk, hk0] using hp
  exact tendsto_nhds_unique_of_eventuallyEq
    ((b65f_transport_converges hU hB γ hc hm).mul_const (G (γ 0)))
    ((b65f_transport_converges hU hA γ hc hm).const_mul (G (γ 1))) he

theorem b65p_loop_transport_gauge (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (A B G : ℂ → E →L[ℂ] E) (U : Set ℂ)
    (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hG : ∀ z ∈ U, HasDerivAt G (B z * G z - G z * A z) z)
    (x : ℂ) (hunit : IsUnit (G x)) :
    ∃ g : (E →L[ℂ] E)ˣ, ∀ γ : Path x x, (∀ s, γ s ∈ U) →
      b65f_transport E B (fun u ↦ γ.extend u) =
        g.val * b65f_transport E A (fun u ↦ γ.extend u) * (g⁻¹).val := by
  obtain ⟨g, hg⟩ := hunit
  refine ⟨g, fun γ hγ ↦ ?_⟩
  have hm : MapsTo γ.extend (Icc 0 1) U := fun u _ ↦ hγ _
  have hh := b65p_transport_gauge E A B G U hU hA hB hG
    γ.extend γ.continuous_extend.continuousOn hm
  rw [Path.extend_zero, Path.extend_one, ← hg] at hh
  have he := congrArg (fun T : E →L[ℂ] E ↦ T * (g⁻¹).val) hh
  simpa only [mul_assoc, Units.val_mul, Units.mul_inv, Units.val_one, mul_one] using he

end HodgeLean.Foundations.Program
