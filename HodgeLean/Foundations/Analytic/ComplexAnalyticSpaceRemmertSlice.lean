import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertDim

/-! # Generic slicing at points of constant fibre dimension

Lane `an-rem`, prefix `anrem_`. For a locally analytic set `Γ ⊆ ℂᴺ` and a linear map `P` whose
fibres through the points of `Γ` near `a` all have dimension `j`, a generic linear slice of
codimension `j` through `a` meets every nearby fibre of `P`, the restriction of `P` to the slice is
proper with finite fibres over a ball, and the slice has dimension at most `q - j` when `Γ` has
dimension at most `q` (Chirka, *Complex Analytic Sets*, §3.7; the openness of finite maps on
components of full dimension does the covering). HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

theorem anrem_norm_append {p q : ℕ} (u : Fin p → ℂ) (v : Fin q → ℂ) :
    ‖Fin.append u v‖ = max ‖u‖ ‖v‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg u))).2 fun i ↦ ?_
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
    · rw [Fin.append_left]; exact (norm_le_pi_norm u i).trans (le_max_left _ _)
    · rw [Fin.append_right]; exact (norm_le_pi_norm v j).trans (le_max_right _ _)
  · refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
      rw [← Fin.append_left u v i]; exact norm_le_pi_norm _ _
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ ?_
      rw [← Fin.append_right u v j]; exact norm_le_pi_norm _ _

/-- Local equations of a set on an open set, with extra linear equations. -/
theorem anrem_locEq_of_eqns {N k : ℕ} {Γ U : Set (Fin N → ℂ)} (hU : IsOpen U)
    {f : Fin k → (Fin N → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hUΓ : ∀ z ∈ U, (z ∈ Γ ↔ ∀ i, f i z = 0)) {p : ℕ} (L : (Fin N → ℂ) →L[ℂ] (Fin p → ℂ))
    (t : Fin p → ℂ) {V : Set (Fin N → ℂ)} (hV : IsOpen V) {z : Fin N → ℂ} (hz : z ∈ U ∩ V) :
    anrem_LocEq (Γ ∩ {z | L z = t} ∩ V) z := by
  refine ⟨U ∩ V, hU.inter hV, hz, k + p, Fin.append f (fun i x ↦ L x i - t i), fun i ↦ ?_,
    fun x hx ↦ ?_⟩
  · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
    · rw [Fin.append_left]; exact (hf i).mono inter_subset_left
    · rw [Fin.append_right]
      intro x _
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) i).analyticAt _).comp
        (L.analyticAt x) |>.sub analyticAt_const
  · simp only [mem_inter_iff, mem_ofPred_eq, hx.2, and_true]
    rw [hUΓ x hx.1]
    constructor
    · rintro ⟨h1, h2⟩ i
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
      · simpa using h1 i
      · simp [h2]
    · intro h
      refine ⟨fun i ↦ by simpa using h (Fin.castAdd p i), funext fun i ↦ ?_⟩
      have := h (Fin.natAdd k i)
      simp only [Fin.append_right] at this
      exact sub_eq_zero.1 this


theorem anrem_locEq_fibre {N k : ℕ} {Γ U : Set (Fin N → ℂ)} (hU : IsOpen U)
    {f : Fin k → (Fin N → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hUΓ : ∀ z ∈ U, (z ∈ Γ ↔ ∀ i, f i z = 0)) {p : ℕ} (L : (Fin N → ℂ) →L[ℂ] (Fin p → ℂ))
    (t : Fin p → ℂ) {z : Fin N → ℂ} (hz : z ∈ U) :
    anrem_LocEq (Γ ∩ {z | L z = t}) z := by
  obtain ⟨U', hU', hzU', m, g, hg, hU'eq⟩ := anrem_locEq_of_eqns hU hf hUΓ L t isOpen_univ
    (z := z) ⟨hz, mem_univ _⟩
  exact ⟨U', hU', hzU', m, g, hg, fun x hx ↦ by rw [← hU'eq x hx]; simp⟩

theorem anrem_locEq_open {N k : ℕ} {Γ U : Set (Fin N → ℂ)} (hU : IsOpen U)
    {f : Fin k → (Fin N → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hUΓ : ∀ z ∈ U, (z ∈ Γ ↔ ∀ i, f i z = 0)) {V : Set (Fin N → ℂ)} (hV : IsOpen V)
    {z : Fin N → ℂ} (hz : z ∈ U ∩ V) : anrem_LocEq (Γ ∩ V) z := by
  refine ⟨U ∩ V, hU.inter hV, hz, k, f, fun i ↦ (hf i).mono inter_subset_left, fun x hx ↦ ?_⟩
  rw [← hUΓ x hx.1]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx.2⟩⟩

/-- A point of a finite set is isolated in it. -/
theorem anrem_isolated_of_finite {N : ℕ} {F : Set (Fin N → ℂ)} (hF : F.Finite)
    {z : Fin N → ℂ} : ∀ᶠ x in 𝓝 z, x ∈ F → x = z := by
  have hc : IsClosed (F \ {z}) := (hF.subset sdiff_subset).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl)] with x hx hxF
  by_contra hne
  exact hx ⟨hxF, hne⟩

/-- **Generic slicing at a point of constant fibre dimension.** -/
theorem anrem_slice_local {N m j q k : ℕ} {Γ U : Set (Fin N → ℂ)} (hU : IsOpen U)
    {f : Fin k → (Fin N → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hUΓ : ∀ z ∈ U, (z ∈ Γ ↔ ∀ i, f i z = 0)) (P : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ))
    {a : Fin N → ℂ} (ha : a ∈ Γ) (haU : a ∈ U)
    (hfib : ∀ z ∈ Γ ∩ U, adim2_dimension N (adim2_germ N (Γ ∩ {x | P x = P z}) z) = j)
    (hdim : ∀ z ∈ Γ ∩ U, adim2_dimension N (adim2_germ N Γ z) ≤ q) :
    ∃ (π : (Fin N → ℂ) →L[ℂ] (Fin j → ℂ)) (ρ r ρ' : ℝ), 0 < ρ ∧ 0 < r ∧ 0 < ρ' ∧
      Metric.closedBall a ρ ⊆ U ∧
      (∀ t ∈ Metric.ball (P a) r,
        {z | z ∈ Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ ∧ P z = t}.Finite) ∧
      (∀ K, IsCompact K → K ⊆ Metric.ball (P a) r →
        IsCompact {z | z ∈ Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ ∧ P z ∈ K}) ∧
      (∀ z ∈ Γ ∩ Metric.ball a ρ', P z ∈ Metric.ball (P a) r →
        ∃ z' ∈ Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ, P z' = P z) ∧
      (∀ z ∈ Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ,
        adim2_dimension N (adim2_germ N (Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ) z) ≤
          ((q - j : ℕ) : WithBot ℕ∞)) := by
  classical
  -- the generic slice
  let S : Bool → Set (Fin N → ℂ) := fun b ↦ cond b (Γ ∩ U) (Γ ∩ {x | P x = P a} ∩ U)
  let e : Bool → ℕ := fun b ↦ cond b q j
  have hlocS : ∀ b, ∀ y ∈ S b, ∃ U' : Set (Fin N → ℂ), IsOpen U' ∧ y ∈ U' ∧ ∃ (m' : ℕ)
      (g : Fin m' → (Fin N → ℂ) → ℂ), (∀ i, AnalyticOnNhd ℂ (g i) U') ∧
        ∀ z ∈ U', (z ∈ S b ↔ ∀ i, g i z = 0) := by
    rintro (_ | _) y hy
    · exact anrem_locEq_of_eqns hU hf hUΓ P (P a) hU ⟨hy.2, hy.2⟩
    · exact anrem_locEq_open hU hf hUΓ hU ⟨hy.2, hy.2⟩
  have hdimS : ∀ b, ∀ y ∈ S b, ∀ Q ∈ (adim2_ideal N (adim2_germ N (S b) y)).minimalPrimes,
      ringKrullDim (AnalyticGerm N ⧸ Q) ≤ (e b : WithBot ℕ∞) := by
    rintro (_ | _) y hy
    · have hPy : P y = P a := hy.1.2
      have : adim2_germ N (S false) y = adim2_germ N (Γ ∩ {x | P x = P y}) y := by
        change adim2_germ N (Γ ∩ {x | P x = P a} ∩ U) y = _
        rw [anrem_germ_inter_nhds _ U y (hU.mem_nhds hy.2), hPy]
      rw [this]
      exact (anrem_dimension_le_iff _ y _).1 (hfib y ⟨hy.1.1, hy.2⟩).le
    · have : adim2_germ N (S true) y = adim2_germ N Γ y :=
        anrem_germ_inter_nhds _ U y (hU.mem_nhds hy.2)
      rw [this]
      exact (anrem_dimension_le_iff _ y _).1 (hdim y hy)
  obtain ⟨π, hπ⟩ := anr_slice S (fun _ ↦ a) e hlocS hdimS j
  -- isolation of the base point in the fibre slice
  have hiso0 : ∀ᶠ z in 𝓝 a, z ∈ S false ∩ {x | π x = π a} → z = a := by
    refine anr_isolated_of_dims _ a ⟨⟨⟨ha, rfl⟩, haU⟩, rfl⟩ fun Q hQ ↦ ?_
    have := hπ false a ⟨⟨⟨ha, rfl⟩, haU⟩, rfl⟩ Q hQ
    simpa [e] using this
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff.1 (hiso0.and (hU.mem_nhds haU))
  set ρ := ρ₀ / 2
  have hρ : 0 < ρ := by positivity
  have hcb : Metric.closedBall a ρ ⊆ U := fun z hz ↦
    (hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (by simp [ρ, hρ₀]))).2
  have hisoρ : ∀ z ∈ Metric.closedBall a ρ, z ∈ Γ → P z = P a → π z = π a → z = a :=
    fun z hz hzΓ hP hπz ↦ (hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz)
      (by simp [ρ, hρ₀]))).1 ⟨⟨⟨hzΓ, hP⟩, hcb hz⟩, hπz⟩
  -- the closed piece and the box radius
  set K := Γ ∩ Metric.closedBall a ρ
  have hKc : IsClosed K := by
    have hcont : ContinuousOn (fun z i ↦ f i z) U :=
      continuousOn_pi.2 fun i ↦ (hf i).continuousOn
    have : K = Metric.closedBall a ρ ∩ (fun z i ↦ f i z) ⁻¹' {0} := by
      ext z
      constructor
      · rintro ⟨hzΓ, hz⟩
        exact ⟨hz, funext fun i ↦ (hUΓ z (hcb hz)).1 hzΓ i⟩
      · rintro ⟨hz, hz0⟩
        exact ⟨(hUΓ z (hcb hz)).2 fun i ↦ congrFun hz0 i, hz⟩
    rw [this]
    exact (hcont.mono hcb).preimage_isClosed_of_isClosed Metric.isClosed_closedBall
      isClosed_singleton
  set G : (Fin N → ℂ) →L[ℂ] (Fin (m + j) → ℂ) := anrem_appendL P π
  have hG : ∀ z, ‖G z - G a‖ = max ‖P z - P a‖ ‖π z - π a‖ := by
    intro z
    simp only [G, anrem_appendL_apply]
    rw [← anrem_norm_append]
    congr 1
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;> simp
  obtain ⟨r, hr, hsph⟩ := anr_box_radius K hKc G a ρ (by
    intro z hz hGz hzρ
    have hGz' := congrArg (fun u ↦ (anrem_fst u, anrem_snd u)) hGz
    simp only [G, anrem_appendL_apply, anrem_fst_append, anrem_snd_append,
      Prod.mk.injEq] at hGz'
    have := hisoρ z (Metric.mem_closedBall.2 (le_of_eq (by rw [dist_eq_norm, hzρ])))
      hz.1 hGz'.1 hGz'.2
    rw [this, sub_self, norm_zero] at hzρ
    exact hρ.ne hzρ)
  -- compactness on the box
  have hbox : ∀ Kt Ks, IsCompact Kt → Kt ⊆ Metric.ball (P a) r → IsCompact Ks →
      Ks ⊆ Metric.ball (π a) r →
      IsCompact {z | z ∈ Γ ∩ Metric.ball a ρ ∧ P z ∈ Kt ∧ π z ∈ Ks} := by
    intro Kt Ks hKt hKtb hKs hKsb
    have heq : {z | z ∈ Γ ∩ Metric.ball a ρ ∧ P z ∈ Kt ∧ π z ∈ Ks} =
        K ∩ (P ⁻¹' Kt ∩ π ⁻¹' Ks) := by
      ext z
      constructor
      · rintro ⟨⟨hzΓ, hz⟩, h1, h2⟩
        exact ⟨⟨hzΓ, Metric.ball_subset_closedBall hz⟩, h1, h2⟩
      · rintro ⟨⟨hzΓ, hz⟩, h1, h2⟩
        refine ⟨⟨hzΓ, ?_⟩, h1, h2⟩
        rcases (Metric.mem_closedBall.1 hz).lt_or_eq with h | h
        · exact h
        · exfalso
          have h3 := hsph z ⟨hzΓ, hz⟩ (by rw [← dist_eq_norm]; exact h)
          rw [hG] at h3
          have h4 : ‖P z - P a‖ < r := by rw [← dist_eq_norm]; exact hKtb h1
          have h5 : ‖π z - π a‖ < r := by rw [← dist_eq_norm]; exact hKsb h2
          exact absurd h3 (not_le.2 (max_lt h4 h5))
    rw [heq]
    exact (isCompact_closedBall a ρ).of_isClosed_subset
      (hKc.inter ((hKt.isClosed.preimage P.continuous).inter
        (hKs.isClosed.preimage π.continuous))) (fun z hz ↦ hz.1.2)
  -- the fibres of the projection on the box are finite
  have hfin : ∀ t ∈ Metric.ball (P a) r, ∀ s ∈ Metric.ball (π a) r,
      {z | z ∈ Γ ∩ Metric.ball a ρ ∧ P z ∈ ({t} : Set _) ∧ π z ∈ ({s} : Set _)}.Finite := by
    intro t ht s hs
    refine adim9_compact_analytic_finite N _ (hbox {t} {s} isCompact_singleton
      (singleton_subset_iff.2 ht) isCompact_singleton (singleton_subset_iff.2 hs)) ?_
    intro x hx
    obtain ⟨U', hU', hxU', m', g, hg, hU'eq⟩ := anrem_locEq_of_eqns hU hf hUΓ G
      (Fin.append t s) Metric.isOpen_ball (z := x) ⟨hcb (Metric.ball_subset_closedBall hx.1.2),
        hx.1.2⟩
    refine ⟨U', hU', hxU', m', g, hg, fun z hz ↦ ?_⟩
    rw [← hU'eq z hz]
    simp only [G, anrem_appendL_apply, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hzΓ, hzb⟩, h1, h2⟩
      exact ⟨⟨hzΓ, by rw [h1, h2]⟩, hzb⟩
    · rintro ⟨⟨hzΓ, hGz⟩, hzb⟩
      obtain ⟨h1, h2⟩ := anrem_append_inj hGz
      exact ⟨⟨hzΓ, hzb⟩, h1, h2⟩
  have hslice_eq : ∀ T : Set (Fin m → ℂ),
      {z | z ∈ Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ ∧ P z ∈ T} =
        {z | z ∈ Γ ∩ Metric.ball a ρ ∧ P z ∈ T ∧ π z ∈ ({π a} : Set _)} := by
    intro T
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    tauto
  set ρ' := min ρ (r / (‖π‖ + 1))
  have hρ' : 0 < ρ' := lt_min hρ (by positivity)
  refine ⟨π, ρ, r, ρ', hρ, hr, hρ', hcb, fun t ht ↦ ?_, fun K hK hKb ↦ ?_, ?_, ?_⟩
  · have := hfin t ht (π a) (Metric.mem_ball_self hr)
    refine this.subset fun z hz ↦ ?_
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff] at hz ⊢
    exact ⟨⟨hz.1.1.1, hz.1.2⟩, hz.2, hz.1.1.2⟩
  · rw [hslice_eq]
    exact hbox K {π a} hK hKb isCompact_singleton
      (singleton_subset_iff.2 (Metric.mem_ball_self hr))
  · rintro z₀ ⟨hz₀Γ, hz₀b⟩ ht₀
    set t₀ := P z₀
    set u := {s | ∃ z ∈ Γ ∩ Metric.ball a ρ, P z = t₀ ∧ π z = s} ∩ Metric.ball (π a) r
    have hπz₀ : π z₀ ∈ Metric.ball (π a) r := by
      rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
      calc ‖π (z₀ - a)‖ ≤ ‖π‖ * ‖z₀ - a‖ := π.le_opNorm _
        _ ≤ ‖π‖ * (r / (‖π‖ + 1)) := by
          gcongr
          rw [← dist_eq_norm]
          exact (Metric.mem_ball.1 hz₀b).le.trans (min_le_right _ _)
        _ < r := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg π]
    have hz₀ρ : z₀ ∈ Metric.ball a ρ := Metric.ball_subset_ball (min_le_left _ _) hz₀b
    have hopen : IsOpen u := by
      rw [isOpen_iff_mem_nhds]
      rintro s ⟨⟨z, ⟨hzΓ, hzb⟩, hPz, hπz⟩, hsb⟩
      have hzU : z ∈ U := hcb (Metric.ball_subset_closedBall hzb)
      have hFs := hfin t₀ ht₀ s hsb
      have hiso : ∀ᶠ x in 𝓝 z, x ∈ Γ ∩ {x | P x = t₀} → π x = π z → x = z := by
        filter_upwards [anrem_isolated_of_finite hFs (z := z),
          Metric.isOpen_ball.mem_nhds hzb] with x h1 h2 hx hπx
        exact h1 ⟨⟨hx.1, h2⟩, hx.2, by rw [mem_singleton_iff, hπx, hπz]⟩
      have hdz : ((j : ℕ) : WithBot ℕ∞) ≤
          adim2_dimension N (adim2_germ N (Γ ∩ {x | P x = t₀}) z) := by
        rw [← hPz, hfib z ⟨hzΓ, hzU⟩]
      have hε : 0 < ρ - dist z a := sub_pos.2 (Metric.mem_ball.1 hzb)
      have hev := anrem_open_image (C := Γ ∩ {x | P x = t₀}) ⟨hzΓ, hPz⟩ (anrem_locEq_fibre hU hf hUΓ P t₀ hzU) π hiso
        hdz hε
      rw [hπz] at hev
      filter_upwards [hev, Metric.isOpen_ball.mem_nhds hsb] with s' ⟨z', hz'C, hz'd, hz'π⟩ hs'
      refine ⟨⟨z', ⟨hz'C.1, ?_⟩, hz'C.2, hz'π⟩, hs'⟩
      rw [Metric.mem_ball]
      calc dist z' a ≤ dist z' z + dist z a := dist_triangle _ _ _
        _ < ρ := by linarith
    have hclosed : closure u ∩ Metric.ball (π a) r ⊆ u := by
      rintro s ⟨hsc, hsb⟩
      have hd : dist s (π a) < r := hsb
      set r' := (dist s (π a) + r) / 2
      have hr's : dist s (π a) < r' := by simp only [r']; linarith
      have hr'r : r' < r := by simp only [r']; linarith
      have hKs : Metric.closedBall (π a) r' ⊆ Metric.ball (π a) r :=
        Metric.closedBall_subset_ball hr'r
      have hcomp := (hbox {t₀} (Metric.closedBall (π a) r') isCompact_singleton
        (singleton_subset_iff.2 ht₀) (isCompact_closedBall _ _) hKs).image π.continuous
      have hsub : u ∩ Metric.ball (π a) r' ⊆
          π '' {z | z ∈ Γ ∩ Metric.ball a ρ ∧ P z ∈ ({t₀} : Set _) ∧
            π z ∈ Metric.closedBall (π a) r'} := by
        rintro s' ⟨⟨⟨z, hz, hPz, hπz⟩, -⟩, hs'⟩
        exact ⟨z, ⟨hz, hPz, by rw [hπz]; exact Metric.ball_subset_closedBall hs'⟩, hπz⟩
      have hs' : s ∈ closure (u ∩ Metric.ball (π a) r') :=
        anr_mem_closure_inter_open hsc Metric.isOpen_ball hr's
      obtain ⟨z, ⟨hz, hPz, -⟩, hπz⟩ := hcomp.isClosed.closure_subset (closure_mono hsub hs')
      exact ⟨⟨z, hz, hPz, hπz⟩, hsb⟩
    have hsub := (convex_ball (π a) r).isPreconnected.subset_of_closure_inter_subset hopen
      ⟨π z₀, hπz₀, ⟨z₀, ⟨hz₀Γ, hz₀ρ⟩, rfl, rfl⟩, hπz₀⟩ hclosed
    obtain ⟨⟨z', ⟨hz'Γ, hz'b⟩, hPz', hπz'⟩, -⟩ := hsub (Metric.mem_ball_self hr)
    exact ⟨z', ⟨⟨hz'Γ, hπz'⟩, hz'b⟩, hPz'⟩
  · rintro z ⟨⟨hzΓ, hzπ⟩, hzb⟩
    have hzU : z ∈ U := hcb (Metric.ball_subset_closedBall hzb)
    have h1 := hπ true z ⟨⟨hzΓ, hzU⟩, hzπ⟩
    have hgerm : adim2_germ N (Γ ∩ {x | π x = π a} ∩ Metric.ball a ρ) z =
        adim2_germ N (S true ∩ {x | π x = π a}) z := by
      rw [anrem_germ_inter_nhds _ _ z (Metric.isOpen_ball.mem_nhds hzb)]
      change _ = adim2_germ N (Γ ∩ U ∩ {x | π x = π a}) z
      rw [show Γ ∩ U ∩ {x | π x = π a} = Γ ∩ {x | π x = π a} ∩ U by
        ext; simp only [mem_inter_iff]; tauto]
      rw [anrem_germ_inter_nhds _ _ z (hU.mem_nhds hzU)]
    rw [hgerm, anrem_dimension_le_iff]
    simpa [e] using h1

end HodgeLean.Foundations.Analytic
