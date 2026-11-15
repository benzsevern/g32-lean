import HodgeLean.Foundations.Program.PrymParabolicIntersectionGluedLoops

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Manifold Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]

/-- Two paths with the same ends inside one convex chart ball have the same path chain. -/
theorem hga_pathChain_chartBall (y : T) (r : ℝ)
    (hr : ball (chartAt ℂ y y) r ⊆ (chartAt ℂ y).target) (g h : C(unitInterval, T))
    (hg : ∀ t, g t ∈ (chartAt ℂ y).source ∧ chartAt ℂ y (g t) ∈ ball (chartAt ℂ y y) r)
    (hh : ∀ t, h t ∈ (chartAt ℂ y).source ∧ chartAt ℂ y (h t) ∈ ball (chartAt ℂ y y) r)
    (h0 : g 0 = h 0) (h1 : g 1 = h 1) : b6m_pathChain g = b6m_pathChain h := by
  let B := ball (chartAt ℂ y y) r
  haveI : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, (hg 0).2⟩
  let j : C(B, T) := ⟨fun z ↦ (chartAt ℂ y).symm z,
    (chartAt ℂ y).continuousOn_symm.comp_continuous continuous_subtype_val (fun z ↦ hr z.2)⟩
  let g' : C(unitInterval, B) := ⟨fun t ↦ ⟨chartAt ℂ y (g t), (hg t).2⟩,
    ((chartAt ℂ y).continuousOn.comp_continuous g.continuous (fun t ↦ (hg t).1)).subtype_mk _⟩
  let h' : C(unitInterval, B) := ⟨fun t ↦ ⟨chartAt ℂ y (h t), (hh t).2⟩,
    ((chartAt ℂ y).continuousOn.comp_continuous h.continuous (fun t ↦ (hh t).1)).subtype_mk _⟩
  have hjg : j.comp g' = g := by
    ext t; exact (chartAt ℂ y).left_inv (hg t).1
  have hjh : j.comp h' = h := by
    ext t; exact (chartAt ℂ y).left_inv (hh t).1
  have := hga_pathChain_contractible j g' h'
    (Subtype.ext (by simp [g', h', h0])) (Subtype.ext (by simp [g', h', h1]))
  rwa [hjg, hjh] at this

/-- Paths glued along the integers, read at `N t`.
Source: `b3Rest_floorPath_contMDiff`. -/
def hga_floorGlue (N : ℕ) (γ : ℤ → ℝ → T) (t : ℝ) : T :=
  γ ⌊(N : ℝ) * t⌋ (Int.fract ((N : ℝ) * t))

theorem hga_floorGlue_apply {N : ℕ} (hN : 0 < N) {γ : ℤ → ℝ → T} {z : ℤ → T}
    (hγ : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))) (k : ℤ) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) : hga_floorGlue N γ ((k + σ) / N) = γ k σ := by
  have hN' : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 hN).ne'
  have e : (N : ℝ) * ((k + σ) / N) = k + σ := by field_simp
  show γ ⌊(N : ℝ) * ((k + σ) / N)⌋ (Int.fract ((N : ℝ) * ((k + σ) / N))) = _
  rw [e]
  rcases hσ.2.lt_or_eq with h1 | h1
  · have hfl : ⌊(k : ℝ) + σ⌋ = k := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [hσ.1]
    rw [Int.fract, hfl]
    congr 1
    ring
  · subst h1
    have hc : (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [hc, Int.floor_intCast, Int.fract_intCast, (hγ (k + 1)).apply_zero, (hγ k).apply_one]

theorem hga_floorGlue_eventually {γ : ℤ → ℝ → T} {z : ℤ → T}
    (hγ : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))) (n : ℤ) :
    ∀ᶠ u in 𝓝 (n : ℝ), γ ⌊u⌋ (Int.fract u) = z n := by
  have h0 : ∀ᶠ v in 𝓝 (n : ℝ), γ n (v - n) = z n := by
    have ht : Tendsto (fun v : ℝ ↦ v - n) (𝓝 (n : ℝ)) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    exact ht.eventually (hγ n).2.1
  have h1 : ∀ᶠ v in 𝓝 (n : ℝ), γ (n - 1) (v - (n - 1)) = z n := by
    have ht : Tendsto (fun v : ℝ ↦ v - (n - 1)) (𝓝 (n : ℝ)) (𝓝 1) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
    have := ht.eventually (hγ (n - 1)).2.2
    simpa only [sub_add_cancel] using this
  have h2 : Ioo ((n : ℝ) - 1) (n + 1) ∈ 𝓝 (n : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [h0, h1, h2] with v hv0 hv1 hv2
  rcases le_or_gt (n : ℝ) v with hle | hlt
  · have hfl : ⌊v⌋ = n := by rw [Int.floor_eq_iff]; exact ⟨hle, hv2.2⟩
    rw [Int.fract, hfl, hv0]
  · have hfl : ⌊v⌋ = n - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hv2.1]
    rw [Int.fract, hfl]
    push_cast
    exact hv1

theorem hga_gridPt_zero (N : ℕ) : hga_gridPt N 0 = 0 :=
  Subtype.ext (by rw [hga_gridPt_val (Nat.zero_le _)]; simp)

theorem hga_gridPt_of_le {N m : ℕ} (hN : 0 < N) (hm : N ≤ m) : hga_gridPt N m = 1 := by
  apply Subtype.ext
  rw [hga_gridPt, Set.projIcc_of_right_le]
  · rfl
  · rw [le_div_iff₀ (Nat.cast_pos.2 hN), one_mul]
    exact_mod_cast hm

theorem hga_affI_zero (a b : unitInterval) : b3Rest2_affI a b 0 = a :=
  Subtype.ext (by simp [b3Rest2_affI])

theorem hga_affI_one (a b : unitInterval) : b3Rest2_affI a b 1 = b :=
  Subtype.ext (by simp [b3Rest2_affI])

/-- **Approximation by a good path.** A path inside an open set `W` is replaced by a good path
inside `W` with the same ends and the same path chain: the chart polygon of a fine cover by
convex chart balls inside `W`. -/
theorem hga_exists_goodPath_approx (W : Set T) (hW : IsOpen W) (p : C(unitInterval, T))
    (hp : ∀ t, p t ∈ W) :
    ∃ q : ℝ → T, b3A_IsGoodPath (E := ℂ) q (p 0) (p 1) ∧ (∀ s, q s ∈ W) ∧
      ∃ hq : Continuous q, b6m_pathChain (hga_unitPath q hq) = b6m_pathChain p := by
  classical
  have hρ : ∀ t : unitInterval, ∃ ρ > 0, ball (chartAt ℂ (p t) (p t)) ρ ⊆
      (chartAt ℂ (p t)).target ∩ (chartAt ℂ (p t)).symm ⁻¹' W := by
    intro t
    have ho : IsOpen ((chartAt ℂ (p t)).target ∩ (chartAt ℂ (p t)).symm ⁻¹' W) :=
      (chartAt ℂ (p t)).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ (p t)).open_target hW
    have hm : chartAt ℂ (p t) (p t) ∈
        (chartAt ℂ (p t)).target ∩ (chartAt ℂ (p t)).symm ⁻¹' W := by
      refine ⟨(chartAt ℂ (p t)).map_source (mem_chart_source ℂ _), ?_⟩
      simp only [mem_preimage, (chartAt ℂ (p t)).left_inv (mem_chart_source ℂ _)]
      exact hp t
    exact Metric.isOpen_iff.mp ho _ hm
  choose ρ hρ0 hρ using hρ
  let c : unitInterval → Set unitInterval := fun i ↦ p ⁻¹' ((chartAt ℂ (p i)).source ∩
    chartAt ℂ (p i) ⁻¹' ball (chartAt ℂ (p i) (p i)) (ρ i))
  have hco : ∀ i, IsOpen (c i) := fun i ↦
    ((chartAt ℂ (p i)).continuousOn.isOpen_inter_preimage (chartAt ℂ (p i)).open_source
      isOpen_ball).preimage p.continuous
  have hcov : (univ : Set unitInterval) ⊆ ⋃ i, c i := fun t _ ↦
    mem_iUnion.2 ⟨t, mem_chart_source ℂ _, by simp [hρ0]⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hco hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := n + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos n
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  have hsel : ∀ k : ℕ, ∃ i : unitInterval, ball (hga_gridPt N k) δ ⊆ c i :=
    fun k ↦ hball _ (mem_univ _)
  choose idx hidx using hsel
  have harc : ∀ k : ℕ, k < N → ∀ t : unitInterval,
      b3Rest2_affI (hga_gridPt N k) (hga_gridPt N (k + 1)) t ∈ c (idx k) := by
    intro k hk t
    apply hidx k
    rw [mem_ball, Subtype.dist_eq]
    change dist (((hga_gridPt N k : ℝ) + t * ((hga_gridPt N (k + 1) : ℝ) -
      (hga_gridPt N k : ℝ)))) (hga_gridPt N k : ℝ) < δ
    rw [hga_gridPt_val hk.le, hga_gridPt_val hk, Real.dist_eq]
    have e : (k : ℝ) / N + (t : ℝ) * (((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) - (k : ℝ) / N =
        (t : ℝ) / N := by
      push_cast; field_simp; ring
    rw [e, abs_of_nonneg (div_nonneg t.2.1 hN.le)]
    calc (t : ℝ) / N ≤ 1 / N := div_le_div_of_nonneg_right t.2.2 hN.le
      _ = 1 / ((n : ℝ) + 1) := by rw [hNdef]; push_cast; ring
      _ < δ := hn
  let x : ℕ → T := fun k ↦ p (idx k)
  let A : ℕ → ℂ := fun k ↦ chartAt ℂ (x k) (p (hga_gridPt N k))
  let B : ℕ → ℂ := fun k ↦ chartAt ℂ (x k) (p (hga_gridPt N (k + 1)))
  have hA : ∀ k, k < N → p (hga_gridPt N k) ∈ (chartAt ℂ (x k)).source ∧
      A k ∈ ball (chartAt ℂ (x k) (x k)) (ρ (idx k)) := by
    intro k hk
    have := harc k hk 0
    rwa [hga_affI_zero] at this
  have hB : ∀ k, k < N → p (hga_gridPt N (k + 1)) ∈ (chartAt ℂ (x k)).source ∧
      B k ∈ ball (chartAt ℂ (x k) (x k)) (ρ (idx k)) := by
    intro k hk
    have := harc k hk 1
    rwa [hga_affI_one] at this
  have hptW : ∀ k, k < N → ∀ τ : ℝ, A k + Real.smoothTransition (3 * τ - 1) • (B k - A k) ∈
      ball (chartAt ℂ (x k) (x k)) (ρ (idx k)) := fun k hk τ ↦
    Convex.add_smul_sub_mem (convex_ball _ _) (hA k hk).2 (hB k hk).2
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  let seg : ℤ → ℝ → T := fun k ↦
    if 0 ≤ k ∧ k < N then fun τ ↦ (chartAt ℂ (x k.toNat)).symm
      (A k.toNat + Real.smoothTransition (3 * τ - 1) • (B k.toNat - A k.toNat))
    else fun _ ↦ if k < 0 then p 0 else p 1
  let z : ℤ → T := fun k ↦ p (hga_gridPt N k.toNat)
  have hgood : ∀ k, b3A_IsGoodPath (E := ℂ) (seg k) (z k) (z (k + 1)) := by
    intro k
    by_cases hk : 0 ≤ k ∧ k < N
    · have hkN : k.toNat < N := by omega
      have hs : segment ℝ (A k.toNat) (B k.toNat) ⊆ (chartAt ℂ (x k.toNat)).target :=
        ((convex_ball _ _).segment_subset (hA _ hkN).2 (hB _ hkN).2).trans
          ((hρ (idx k.toNat)).trans inter_subset_left)
      have h := b3A_isGoodPath_segment (E := ℂ) (x k.toNat) (A k.toNat) (B k.toNat) hs
      have e1 : (chartAt ℂ (x k.toNat)).symm (A k.toNat) = z k :=
        (chartAt ℂ (x k.toNat)).left_inv (hA _ hkN).1
      have e2 : (chartAt ℂ (x k.toNat)).symm (B k.toNat) = z (k + 1) := by
        have : (k + 1).toNat = k.toNat + 1 := by omega
        simp only [z, this]
        exact (chartAt ℂ (x k.toNat)).left_inv (hB _ hkN).1
      rw [e1, e2] at h
      have hs : seg k = fun τ ↦ (chartAt ℂ (x k.toNat)).symm
          (A k.toNat + Real.smoothTransition (3 * τ - 1) • (B k.toNat - A k.toNat)) := if_pos hk
      rw [hs]
      exact h
    · by_cases hneg : k < 0
      · have e1 : z k = p 0 := by
          simp only [z, show k.toNat = 0 by omega, hga_gridPt_zero]
        have e2 : z (k + 1) = p 0 := by
          simp only [z, show (k + 1).toNat = 0 by omega, hga_gridPt_zero]
        have : seg k = fun _ ↦ p 0 := by
          simp only [seg]; rw [if_neg hk]; funext _; rw [if_pos hneg]
        rw [this, e1, e2]
        exact b3A_isGoodPath_const _
      · have e1 : z k = p 1 := by
          simp only [z]; rw [hga_gridPt_of_le hNpos (by omega)]
        have e2 : z (k + 1) = p 1 := by
          simp only [z]; rw [hga_gridPt_of_le hNpos (by omega)]
        have : seg k = fun _ ↦ p 1 := by
          simp only [seg]; rw [if_neg hk]; funext _; rw [if_neg hneg]
        rw [this, e1, e2]
        exact b3A_isGoodPath_const _
  let q : ℝ → T := hga_floorGlue N seg
  have hqC : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 q :=
    (b3Rest_floorPath_contMDiff (E := ℂ) seg z hgood).comp
      ((contDiff_const.mul contDiff_id).contMDiff)
  have hqc : Continuous q := hqC.continuous
  have hev : ∀ m : ℤ, ∀ᶠ t in 𝓝 ((m : ℝ) / N), q t = z m := by
    intro m
    have ht : Tendsto (fun t : ℝ ↦ (N : ℝ) * t) (𝓝 ((m : ℝ) / N)) (𝓝 (m : ℝ)) := by
      have hc : Continuous (fun t : ℝ ↦ (N : ℝ) * t) := by fun_prop
      have := hc.tendsto ((m : ℝ) / N)
      rwa [mul_div_cancel₀ _ hN.ne'] at this
    exact ht.eventually (hga_floorGlue_eventually hgood m)
  have hz0 : z 0 = p 0 := by simp [z, hga_gridPt_zero]
  have hzN : z N = p 1 := by
    simp only [z]; rw [hga_gridPt_of_le hNpos (by simp)]
  refine ⟨q, ⟨hqC, ?_, ?_⟩, ?_, hqc, ?_⟩
  · have := hev 0
    simp only [Int.cast_zero, zero_div] at this
    filter_upwards [this] with t ht
    rw [ht, hz0]
  · have := hev N
    simp only [Int.cast_natCast, div_self hN.ne'] at this
    filter_upwards [this] with t ht
    rw [ht, hzN]
  · have hseg : ∀ k τ, seg k τ ∈ W := by
      intro k τ
      by_cases hk : 0 ≤ k ∧ k < N
      · have hkN : k.toNat < N := by omega
        simp only [seg]
        rw [if_pos hk]
        exact ((hρ (idx k.toNat)) (hptW _ hkN τ)).2
      · simp only [seg]
        rw [if_neg hk]
        split_ifs
        · exact hp 0
        · exact hp 1
    intro s
    exact hseg _ _
  · rw [hga_pathChain_subdivide _ N hNpos, hga_pathChain_subdivide p N hNpos]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hkz : (0 : ℤ) ≤ (k : ℤ) ∧ (k : ℤ) < N := ⟨by positivity, by exact_mod_cast hkN⟩
    let sk : C(unitInterval, T) := ⟨fun τ ↦ (chartAt ℂ (x k)).symm
        (A k + Real.smoothTransition (3 * (τ : ℝ) - 1) • (B k - A k)),
      ((hgood k).1.continuous.comp continuous_subtype_val).congr (fun τ ↦ by
        simp only [Function.comp_apply, seg]
        rw [if_pos hkz, Int.toNat_natCast])⟩
    have e1 : b6m_pathChain (b3Rest2_restr (hga_unitPath q hqc) (hga_gridPt N k)
        (hga_gridPt N (k + 1))) = b6m_pathChain sk := by
      apply hga_pathChain_congr
      intro τ
      simp only [b3Rest2_restr_apply, b3Rest2_affI, hga_unitPath, ContinuousMap.coe_mk]
      rw [hga_gridPt_val hkN.le, hga_gridPt_val hkN]
      have e : (k : ℝ) / N + (τ : ℝ) * (((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) =
          (((k : ℤ) : ℝ) + τ) / N := by
        push_cast; field_simp; ring
      show hga_floorGlue N seg _ = _
      rw [e, hga_floorGlue_apply hNpos hgood (k : ℤ) ⟨τ.2.1, τ.2.2⟩]
      simp only [seg]
      rw [if_pos hkz, Int.toNat_natCast]
      rfl
    rw [e1]
    apply hga_pathChain_chartBall (x k) (ρ (idx k)) ((hρ (idx k)).trans inter_subset_left)
    · intro τ
      have hm := hptW k hkN τ
      have ht := (hρ (idx k) hm).1
      refine ⟨(chartAt ℂ (x k)).map_target ht, ?_⟩
      change chartAt ℂ (x k) ((chartAt ℂ (x k)).symm _) ∈ _
      rw [(chartAt ℂ (x k)).right_inv ht]
      exact hm
    · exact fun t ↦ harc k hkN t
    · change (chartAt ℂ (x k)).symm (A k + Real.smoothTransition (3 * ((0 : unitInterval) : ℝ) - 1) •
        (B k - A k)) = p (b3Rest2_affI _ _ 0)
      rw [hga_affI_zero, Real.smoothTransition.zero_of_nonpos (by norm_num), zero_smul, add_zero]
      exact (chartAt ℂ (x k)).left_inv (hA k hkN).1
    · change (chartAt ℂ (x k)).symm (A k + Real.smoothTransition (3 * ((1 : unitInterval) : ℝ) - 1) •
        (B k - A k)) = p (b3Rest2_affI _ _ 1)
      rw [hga_affI_one, Real.smoothTransition.one_of_one_le (by norm_num), one_smul,
        add_sub_cancel]
      exact (chartAt ℂ (x k)).left_inv (hB k hkN).1

#print axioms hga_exists_goodPath_approx
#print axioms hga_affI_one
#print axioms hga_affI_zero
#print axioms hga_gridPt_of_le
#print axioms hga_gridPt_zero
#print axioms hga_floorGlue_eventually
#print axioms hga_floorGlue_apply
#print axioms hga_floorGlue
#print axioms hga_pathChain_chartBall
end HodgeLean.Foundations.Program
