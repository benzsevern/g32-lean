import HodgeLean.Foundations.Program.FuchsianSystem
import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsRational
import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsDefs

/-! # Transport under change of variables, coefficient agreement and the regular domain

Fine dyadic polygons of a path and of its image agree segment by segment; the printed pullback
coefficient and the regular domain; the covering index bound.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- On a disc about `u` whose image lies in a regular disc of `A`, the segment transport of
the pulled-back coefficient is the segment transport of `A` between the image points. -/
theorem b65t_segment_pull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {φ : ℂ → ℂ} {u v : ℂ} {δ ρ : ℝ}
    (hδ : 0 < δ) (hA : AnalyticOnNhd ℂ A (ball (φ u) ρ))
    (hφ : AnalyticOnNhd ℂ φ (ball u δ)) (hmaps : MapsTo φ (ball u δ) (ball (φ u) ρ))
    (hv : v ∈ ball u δ) :
    b65f_segment E (b65t_pull E φ A) u v = b65f_segment E A (φ u) (φ v) := by
  have hpull : AnalyticOnNhd ℂ (b65t_pull E φ A) (ball u δ) := by
    intro z hz
    exact (hφ.deriv z hz).smul ((hA (φ z) (hmaps hz)).comp (hφ z hz))
  have hZ : ∀ z ∈ ball u δ, HasDerivAt (fun w ↦ b65f_segment E A (φ u) (φ w))
      (b65t_pull E φ A z * b65f_segment E A (φ u) (φ z)) z := by
    intro z hz
    have h1 := b65f_segment_hasDerivAt hA (hmaps hz)
    have h2 := ((hφ z hz).differentiableAt).hasDerivAt
    have := h1.scomp z h2
    rw [b65t_pull, smul_mul_assoc]
    exact this
  have h := b65f_segment_propagates hδ hpull hZ hv
  rwa [b65f_segment_initial, mul_one] at h

/-- Transports agree when the dyadic polygons eventually agree segment by segment. -/
theorem b65t_transport_eq_of_segments {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A₁ A₂ : ℂ → E →L[ℂ] E) (γ₁ γ₂ : ℝ → ℂ)
    (h : ∃ N : ℕ, ∀ n ≥ N, ∀ i : ℕ, i < 2 ^ n →
      b65f_segment E A₁ (γ₁ ((i : ℝ) / (2 : ℝ) ^ n)) (γ₁ (((i : ℝ) + 1) / (2 : ℝ) ^ n)) =
        b65f_segment E A₂ (γ₂ ((i : ℝ) / (2 : ℝ) ^ n)) (γ₂ (((i : ℝ) + 1) / (2 : ℝ) ^ n))) :
    b65f_transport E A₁ γ₁ = b65f_transport E A₂ γ₂ := by
  obtain ⟨N, hN⟩ := h
  have he : b65f_polygon E A₁ γ₁ =ᶠ[atTop] b65f_polygon E A₂ γ₂ := by
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
    unfold b65f_polygon
    congr 3
    funext i
    exact hN n hn _ i.isLt
  unfold b65f_transport limUnder
  rw [Filter.map_congr he]

/-- Dyadic sample points of a curve continuous on the unit interval are eventually near each other. -/
theorem b65t_dyadic_near (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : ℕ, i < 2 ^ n →
      (i : ℝ) / (2 : ℝ) ^ n ∈ Icc (0 : ℝ) 1 ∧
      dist (γ (((i : ℝ) + 1) / (2 : ℝ) ^ n)) (γ ((i : ℝ) / (2 : ℝ) ^ n)) < δ := by
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) δ hδ
  have hlim : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨N, fun n hn i hi ↦ ?_⟩
  have hk : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hile : (i : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.succ_le_of_lt hi)
  have h0 : (i : ℝ) / (2 : ℝ) ^ n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hk.le, (div_le_one hk).mpr (by linarith)⟩
  have h1 : ((i : ℝ) + 1) / (2 : ℝ) ^ n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by positivity) hk.le, (div_le_one hk).mpr hile⟩
  refine ⟨h0, he _ h1 _ h0 ?_⟩
  rw [Real.dist_eq, div_sub_div_same, add_sub_cancel_left, abs_of_nonneg (by positivity)]
  simpa only [one_div] using hN n hn

theorem b65t_transport_pullback_proof (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ V)
    (hmaps : MapsTo φ V U) (x y : V) (γ : Path x y) :
    b65f_transport E (b65t_pull E φ A) (fun t ↦ (γ.extend t).val) =
      b65f_transport E A (fun t ↦ φ (γ.extend t).val) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let c : ℝ → ℂ := fun t ↦ (γ.extend t).val
  have hc : Continuous c := continuous_subtype_val.comp γ.continuous_extend
  have hcV : ∀ t, c t ∈ V := fun t ↦ (γ.extend t).property
  let K := c '' Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image hc
  have hKV : K ⊆ V := by rintro _ ⟨t, -, rfl⟩; exact hcV t
  have hφK : IsCompact (φ '' K) := hK.image_of_continuousOn (hφ.continuousOn.mono hKV)
  obtain ⟨ρ, hρ, hρU⟩ := hφK.exists_thickening_subset_open hU
    (by rintro _ ⟨z, hz, rfl⟩; exact hmaps (hKV hz))
  obtain ⟨δ₀, hδ₀, hδ₀V⟩ := hK.exists_thickening_subset_open hV hKV
  have hL : IsCompact (cthickening (δ₀ / 2) K) := hK.cthickening
  have hLV : cthickening (δ₀ / 2) K ⊆ V :=
    (cthickening_subset_thickening' hδ₀ (by linarith) K).trans hδ₀V
  obtain ⟨δ₁, hδ₁, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (hL.uniformContinuousOn_of_continuous (hφ.continuousOn.mono hLV)) ρ hρ
  let δ := min (δ₀ / 2) δ₁
  have hδ : 0 < δ := lt_min (by linarith) hδ₁
  obtain ⟨N, hN⟩ := b65t_dyadic_near c hc.continuousOn hδ
  apply b65t_transport_eq_of_segments
  refine ⟨N, fun n hn i hi ↦ ?_⟩
  obtain ⟨ht, hd⟩ := hN n hn i hi
  set u := c ((i : ℝ) / (2 : ℝ) ^ n)
  have huK : u ∈ K := mem_image_of_mem c ht
  have hball : ball u δ ⊆ cthickening (δ₀ / 2) K := fun z hz ↦
    (ball_subset_closedBall.trans (closedBall_subset_cthickening huK _))
      (ball_subset_ball (min_le_left _ _) hz)
  apply b65t_segment_pull (ρ := ρ) hδ
  · exact hA.mono ((ball_subset_thickening (mem_image_of_mem φ huK) ρ).trans hρU)
  · exact hφ.mono (hball.trans hLV)
  · intro z hz
    exact mem_ball.mpr (hu z (hball hz) u (self_subset_cthickening K huK)
      ((mem_ball.mp hz).trans_le (min_le_right _ _)))
  · exact mem_ball.mpr hd

/-- Iterated integrals along a segment only see the coefficient on that segment. -/
theorem b65t_iterated_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A₁ A₂ : ℂ → E →L[ℂ] E} {u v : ℂ}
    (h : ∀ q ∈ Icc (0 : ℝ) 1, A₁ (u + (q : ℂ) * (v - u)) = A₂ (u + (q : ℂ) * (v - u))) :
    ∀ m : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, b65f_iterated E A₁ u v m t = b65f_iterated E A₂ u v m t := by
  intro m
  induction m with
  | zero => intro t _; rfl
  | succ m ih =>
    intro t ht
    simp only [b65f_iterated]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le ht.1] at hq
    have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans ht.2⟩
    simp only [h q hq', ih q hq']

theorem b65t_segment_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A₁ A₂ : ℂ → E →L[ℂ] E} {u v : ℂ}
    (h : ∀ q ∈ Icc (0 : ℝ) 1, A₁ (u + (q : ℂ) * (v - u)) = A₂ (u + (q : ℂ) * (v - u))) :
    b65f_segment E A₁ u v = b65f_segment E A₂ u v := by
  unfold b65f_segment
  congr 1
  funext m
  exact b65t_iterated_congr h m 1 ⟨zero_le_one, le_rfl⟩

/-- Coefficients that agree on an open set have the same transport along paths in it. -/
theorem b65t_transport_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A₁ A₂ : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U) (hA : EqOn A₁ A₂ U)
    (c : ℝ → ℂ) (hc : ContinuousOn c (Icc 0 1)) (hm : MapsTo c (Icc 0 1) U) :
    b65f_transport E A₁ c = b65f_transport E A₂ c := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.image_of_continuousOn hc).exists_thickening_subset_open
    hU (image_subset_iff.mpr hm)
  obtain ⟨N, hN⟩ := b65t_dyadic_near c hc hδ
  apply b65t_transport_eq_of_segments
  refine ⟨N, fun n hn i hi ↦ b65t_segment_congr fun q hq ↦ hA ?_⟩
  obtain ⟨ht, hd⟩ := hN n hn i hi
  apply (ball_subset_thickening (mem_image_of_mem c ht) δ).trans hsub
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, ← dist_eq_norm]
  have : ‖(q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq.1]; exact hq.2
  calc ‖(q : ℂ)‖ * dist _ _ ≤ 1 * dist _ _ := by gcongr
    _ < δ := by rw [one_mul]; exact hd

theorem b65t_four_open : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} :=
  (isOpen_ne.inter (isOpen_ne.inter isOpen_ne))

theorem b65t_A_analytic : AnalyticOnNhd ℂ b65r_A {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
  rintro z ⟨h0, h5, h7⟩
  have h5' : z - 5 ≠ 0 := sub_ne_zero.mpr h5
  have h7' : z + 7 ≠ 0 := by
    intro h; apply h7; linear_combination h
  unfold b65r_A
  apply AnalyticAt.add
  apply AnalyticAt.add
  · exact (analyticAt_id.inv h0).smul analyticAt_const
  · exact ((analyticAt_id.sub analyticAt_const).inv h5').smul analyticAt_const
  · exact ((analyticAt_id.add analyticAt_const).inv h7').smul analyticAt_const

theorem b65t_regular_open : IsOpen b65s_regular := by
  have hc5 : Continuous (b65r_P 5) := by unfold b65r_P; fun_prop
  have hc7 : Continuous (b65r_P (-7)) := by unfold b65r_P; fun_prop
  exact isOpen_ne.inter (isOpen_ne.inter (isOpen_ne.inter (isOpen_ne.inter
    ((isOpen_ne_fun hc5 continuous_const).inter (isOpen_ne_fun hc7 continuous_const)))))

theorem b65t_den_ne {s : ℂ} (h1 : s ≠ 1) (h2 : s ≠ -2) : (s - 1) ^ 3 * (s + 2) ^ 3 ≠ 0 := by
  have a : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have b : s + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  exact mul_ne_zero (pow_ne_zero _ a) (pow_ne_zero _ b)

theorem b65t_phi_analytic : AnalyticOnNhd ℂ b65r_phi b65s_regular := by
  rintro s ⟨-, -, h1, h2, -, -⟩
  unfold b65r_phi
  apply AnalyticAt.div (f := fun s : ℂ ↦ s ^ 2 * (s - 3) ^ 4)
    (g := fun s : ℂ ↦ (s - 1) ^ 3 * (s + 2) ^ 3) _ _ (b65t_den_ne h1 h2) <;> fun_prop

theorem b65t_phi_maps : MapsTo b65r_phi b65s_regular {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
  rintro s ⟨h0, h3, h1, h2, h5, h7⟩
  have hD := b65t_den_ne h1 h2
  have h3' : s - 3 ≠ 0 := sub_ne_zero.mpr h3
  refine ⟨?_, ?_, ?_⟩
  · unfold b65r_phi
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h3')) hD
  · intro h
    apply h5
    unfold b65r_phi at h
    rw [div_eq_iff hD] at h
    unfold b65r_P
    linear_combination h
  · intro h
    apply h7
    unfold b65r_phi at h
    rw [div_eq_iff hD] at h
    unfold b65r_P
    linear_combination h

theorem b65t_pullback_transport_proof (x y : b65s_regular) (γ : Path x y) :
    b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ b65r_phi (γ.extend t).val) := by
  have hc : Continuous (fun t ↦ (γ.extend t).val) :=
    continuous_subtype_val.comp γ.continuous_extend
  rw [b65t_transport_congr (A₂ := b65t_pull (Fin 4 → ℂ) b65r_phi b65r_A) b65t_regular_open
    (fun s hs ↦ b65t_pullback_formula s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
      hs.2.2.2.2.2) _ hc.continuousOn (fun t _ ↦ (γ.extend t).property)]
  exact b65t_transport_pullback_proof (Fin 4 → ℂ) _ _ b65t_four_open b65t_regular_open b65r_A
    b65t_A_analytic b65r_phi b65t_phi_analytic b65t_phi_maps x y γ

theorem b65t_covering_index_proof {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsCoveringMap p) (e : E) (hfin : (p ⁻¹' {p e}).Finite) :
    0 < (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index ∧
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index ≤ Nat.card (p ⁻¹' {p e}) := by
  let _ := hp.fundamentalGroupMulAction (p e)
  let e' : p ⁻¹' {p e} := ⟨e, rfl⟩
  have hrange : (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range =
      MulAction.stabilizer (FundamentalGroup B (p e)) e' := by
    ext γ
    constructor
    · rintro ⟨δ, rfl⟩
      exact hp.monodromy_map δ.asHom
    · intro hγ
      have hγ' : hp.monodromy γ.asHom e' = e' := hγ
      obtain ⟨γ₀, hq⟩ := Quotient.exists_rep γ.asHom
      have h0 : γ₀ 0 = p e := γ₀.source
      have h1 : hp.liftPath γ₀ e h0 1 = e := by
        have := congrArg Subtype.val hγ'
        rw [← hq] at this
        exact this
      let Γ : Path e e := ⟨hp.liftPath γ₀ e h0, hp.liftPath_zero .., h1⟩
      refine ⟨FundamentalGroup.fromPath ⟦Γ⟧, ?_⟩
      have hΓ : Γ.map hp.continuous = γ₀ := by
        ext t
        exact congrFun (hp.liftPath_lifts γ₀ e h0) t
      change FundamentalGroup.fromPath ⟦Γ.map hp.continuous⟧ = γ
      rw [hΓ]
      exact congrArg FundamentalGroup.fromPath hq
  have hfin' : Finite (p ⁻¹' {p e}) := hfin.to_subtype
  rw [hrange]
  have hi := MulAction.index_stabilizer (FundamentalGroup B (p e)) e'
  rw [hi]
  refine ⟨(Set.ncard_pos (Set.toFinite _)).mpr ⟨e', MulAction.mem_orbit_self e'⟩, ?_⟩
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _)

/-- The polynomial `b65r_P ε`.
Source: G32 v0.16, §5.2, P₅ and P₋₇. -/
def b65t_Ppoly (ε : ℂ) : ℂ[X] := X ^ 2 * (X - C 3) ^ 4 - C ε * (X - C 1) ^ 3 * (X + C 2) ^ 3

theorem b65t_Ppoly_eval (ε s : ℂ) : (b65t_Ppoly ε).eval s = b65r_P ε s := by
  simp [b65t_Ppoly, b65r_P, mul_assoc]

theorem b65t_Ppoly_ne_zero (ε : ℂ) : b65t_Ppoly ε ≠ 0 := by
  intro h
  have := b65t_Ppoly_eval ε 1
  rw [h, eval_zero] at this
  norm_num [b65r_P] at this

theorem b65t_P5_root : ∃ a : ℂ, b65r_P 5 a = 0 := by
  have hdeg : 0 < degree (b65t_Ppoly 5) := by
    by_contra hle
    push Not at hle
    obtain ⟨c, hc⟩ : ∃ c, b65t_Ppoly 5 = C c := ⟨_, eq_C_of_degree_le_zero hle⟩
    have h0 := b65t_Ppoly_eval 5 0
    have h1 := b65t_Ppoly_eval 5 1
    rw [hc, eval_C] at h0 h1
    norm_num [b65r_P] at h0 h1
    rw [h0] at h1
    norm_num at h1
  obtain ⟨a, ha⟩ := Complex.exists_root hdeg
  exact ⟨a, by rw [← b65t_Ppoly_eval]; exact ha⟩

/-- The singular points of the pulled-back coefficient.
Source: G32 v0.16, §5.4; `b65s_regular`. -/
def b65t_bad : Set ℂ :=
  {0, 3, 1, -2} ∪ {z | b65r_P 5 z = 0} ∪ {z | b65r_P (-7) z = 0}

theorem b65t_regular_eq : b65s_regular = b65t_badᶜ := by
  ext z
  simp only [b65s_regular, b65t_bad, mem_ofPred_eq, mem_compl_iff, mem_union, mem_insert_iff,
    mem_singleton_iff]
  tauto

theorem b65t_bad_finite : b65t_bad.Finite := by
  have h : ∀ ε : ℂ, {z | b65r_P ε z = 0}.Finite := by
    intro ε
    have := Polynomial.finite_setOfPred_isRoot (b65t_Ppoly_ne_zero ε)
    simpa [IsRoot, b65t_Ppoly_eval] using this
  exact ((Set.toFinite _).union (h 5)).union (h (-7))

theorem b65t_regular_pathConnected : IsPathConnected b65s_regular := by
  rw [b65t_regular_eq]
  apply b65t_bad_finite.countable.isPathConnected_compl_of_one_lt_rank
  rw [Complex.rank_real_complex]
  norm_num

theorem b65t_pullback_analytic : AnalyticOnNhd ℂ b65r_pullback b65s_regular := by
  have hpull : AnalyticOnNhd ℂ (b65t_pull (Fin 4 → ℂ) b65r_phi b65r_A) b65s_regular := by
    intro z hz
    exact (b65t_phi_analytic.deriv z hz).smul
      ((b65t_A_analytic (b65r_phi z) (b65t_phi_maps hz)).comp (b65t_phi_analytic z hz))
  exact hpull.congr b65t_regular_open (fun s hs ↦ (b65t_pullback_formula s hs.1 hs.2.1
    hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2).symm)

theorem b65t_transport_congr_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) {γ₁ γ₂ : ℝ → ℂ} (h : EqOn γ₁ γ₂ (Icc 0 1)) :
    b65f_transport E A γ₁ = b65f_transport E A γ₂ := by
  apply b65t_transport_eq_of_segments
  refine ⟨0, fun n _ i hi ↦ ?_⟩
  have hk : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hile : (i : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.succ_le_of_lt hi)
  rw [h ⟨div_nonneg (by positivity) hk.le, (div_le_one hk).mpr (by linarith)⟩,
    h ⟨div_nonneg (by positivity) hk.le, (div_le_one hk).mpr hile⟩]

theorem b65t_transport_refl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) {U : Set ℂ} (x : U) :
    b65f_transport E A (fun t ↦ ((Path.refl x).extend t).val) = 1 := by
  have hp : ∀ N, b65f_polygon E A (fun t ↦ ((Path.refl x).extend t).val) N = 1 := by
    intro N
    simp [b65f_polygon, b65f_segment_initial]
  unfold b65f_transport
  rw [show b65f_polygon E A (fun t ↦ ((Path.refl x).extend t).val) = fun _ ↦ 1 from funext hp]
  exact tendsto_const_nhds.limUnder_eq

end HodgeLean.Foundations.Program
