import HodgeLean.Foundations.Program.FuchsianSystemConvergence

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65f_reverseProduct_intertwines {M : Type*} [Monoid M]
    (D G V : ℕ → M) (n : ℕ)
    (h : ∀ i < n, D i * V i = V (i + 1) * G i) :
    b65f_reverseProduct D n * V 0 = V n * b65f_reverseProduct G n := by
  induction n with
  | zero => simp [b65f_reverseProduct]
  | succ n ih =>
    rw [b65f_reverseProduct_succ, mul_assoc, ih (fun i hi ↦ h i (by omega)),
      ← mul_assoc, h n (by omega), mul_assoc, ← b65f_reverseProduct_succ]

theorem b65f_transport_converges {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A U) (γ : ℝ → ℂ)
    (hc : ContinuousOn γ (Icc 0 1)) (hm : MapsTo γ (Icc 0 1) U) :
    Tendsto (b65f_polygon E A γ) atTop (𝓝 (b65f_transport E A γ)) := by
  obtain ⟨N, _, hs⟩ := b65f_polygon_stabilizes hU hA γ hc hm
  have he : b65f_polygon E A γ =ᶠ[atTop] (fun _ ↦ b65f_polygon E A γ N) :=
    eventually_atTop.mpr ⟨N, hs⟩
  have ht := tendsto_const_nhds.congr' he.symm
  unfold b65f_transport
  rw [ht.limUnder_eq]
  exact ht

theorem b65f_nearby_paths_transport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A U) {x y : U} (γ δ : Path x y)
    {r : ℝ} (hr : 0 < r)
    (hball : ∀ t ∈ Icc (0 : ℝ) 1, ball (γ.extend t).val r ⊆ U)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      dist (δ.extend t).val (γ.extend t).val < r / 16) :
    b65f_transport E A (fun t ↦ (δ.extend t).val) =
      b65f_transport E A (fun t ↦ (γ.extend t).val) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let c : ℝ → ℂ := fun t ↦ (γ.extend t).val
  let d : ℝ → ℂ := fun t ↦ (δ.extend t).val
  have hc : Continuous c := continuous_subtype_val.comp γ.continuous_extend
  have hd : Continuous d := continuous_subtype_val.comp δ.continuous_extend
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn) (r / 16) (by positivity)
  have hlim : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have heq : b65f_polygon E A d =ᶠ[atTop] b65f_polygon E A c := by
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
    let k := 2 ^ N
    have hk : 0 < k := pow_pos (by norm_num) N
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hkR : (k : ℝ) = (2 : ℝ) ^ N := by simp [k]
    have ht (i : ℕ) (hi : i ≤ k) : (i : ℝ) / k ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one (by positivity : (0 : ℝ) < k)).mpr (by exact_mod_cast hi)
    let G : ℕ → E →L[ℂ] E := fun i ↦
      b65f_segment E A (c ((i : ℝ) / k)) (c (((i : ℝ) + 1) / k))
    let D : ℕ → E →L[ℂ] E := fun i ↦
      b65f_segment E A (d ((i : ℝ) / k)) (d (((i : ℝ) + 1) / k))
    let V : ℕ → E →L[ℂ] E := fun i ↦
      b65f_segment E A (c ((i : ℝ) / k)) (d ((i : ℝ) / k))
    have hv0 : V 0 = 1 := by simp [V, c, d, b65f_segment_initial]
    have hvk : V k = 1 := by simp [V, c, d, hk0, b65f_segment_initial]
    have hs : ∀ i < k, D i * V i = V (i + 1) * G i := by
      intro i hi
      have hi0 := ht i hi.le
      have hi1 : ((i : ℝ) + 1) / k ∈ Icc (0 : ℝ) 1 := by
        exact_mod_cast ht (i + 1) (by omega)
      have hdtime : dist (((i : ℝ) + 1) / k) ((i : ℝ) / k) < ε := by
        rw [Real.dist_eq, div_sub_div_same, add_sub_cancel_left, abs_of_nonneg (by positivity)]
        simpa [one_div, hkR] using hN
      have hinc := he _ hi1 _ hi0 hdtime
      have h0 := hclose _ hi0
      have h1 := hclose _ hi1
      have hdiag : dist (d (((i : ℝ) + 1) / k)) (c ((i : ℝ) / k)) < r / 4 := by
        have hh := dist_triangle (d (((i : ℝ) + 1) / k))
          (c (((i : ℝ) + 1) / k)) (c ((i : ℝ) / k))
        change dist (d _) (c _) < r / 16 at h1
        linarith
      have ha := hA.mono (hball _ hi0)
      have hleft := b65f_segment_local_cocycle hr ha
        (show dist (d ((i : ℝ) / k)) (c ((i : ℝ) / k)) < r / 4 by
          change dist (d _) (c _) < r / 16 at h0; linarith) hdiag
      have hright := b65f_segment_local_cocycle hr ha
        (show dist (c (((i : ℝ) + 1) / k)) (c ((i : ℝ) / k)) < r / 4 by linarith) hdiag
      simpa [D, G, V, Nat.cast_add, Nat.cast_one] using hleft.trans hright.symm
    have hp := b65f_reverseProduct_intertwines D G V k hs
    rw [hv0, hvk, mul_one, one_mul] at hp
    simpa [b65f_polygon, b65f_reverseProduct, D, G, hkR] using hp
  have htγ := b65f_transport_converges hU hA c hc.continuousOn (fun t _ ↦ (γ.extend t).property)
  have htδ := b65f_transport_converges hU hA d hd.continuousOn (fun t _ ↦ (δ.extend t).property)
  exact tendsto_nhds_unique htδ (htγ.congr' heq.symm)

end HodgeLean.Foundations.Program
