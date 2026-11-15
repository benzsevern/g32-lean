import HodgeLean.Foundations.Program.CurveJacobianRest2Shift
import HodgeLean.Foundations.Program.CurveJacobianRest2Rank

/-! # Track B3, lane Rest2: dual forms compute intersection numbers

* `b3Rest2_arc_degree`: the smeared arc of a piece `P|[a, b]` of a loop, integrated along a `C¹`
  path `δ` over `[s₀, s₁]`, is `(∫ ρ_ε) Σ sign (P' · δ')` over the crossings `P t = δ s`, for small
  `ε`, if the crossings are finite, transverse, and none sits at an end of either interval
  (`b3Rest2_degree` in the chart of the arc);
* `b3Rest2_key`: for transverse loops `γ`, `δ` there is a dual form `η` of `γ` with
  `∫_δ η = γ · δ`. Shift `γ` by a parameter `a` such that no crossing parameter differs from `a`
  by a rational number, cut the shifted loop into arcs at the points `k / N` of a chart cover
  (none of them is on `δ`), take the dual form built from the smeared arcs with junction
  corrections supported off `δ`, and integrate along `δ` over a period `[s₀, s₀ + 1]` starting
  off `γ`: each arc contributes its signed crossings, and the crossings of the arcs correspond to
  those of `γ` and `δ` in `[0, 1)²`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Rest2_pt_injOn (hE : Module.finrank ℂ E = 1) (x : C) {p p' : C}
    (hp : p ∈ (chartAt E x).source) (hp' : p' ∈ (chartAt E x).source)
    (h : b3Rest_pt hE x p = b3Rest_pt hE x p') : p = p' := by
  have h1 : chartAt E x p = chartAt E x p' := by
    have := congrArg (b3Rest_ζ hE x) h
    rwa [b3Rest_ζ_pt, b3Rest_ζ_pt] at this
  exact (chartAt E x).injOn hp hp' h1

set_option maxHeartbeats 400000 in
/-- **The degree of a smeared arc of a loop along a transverse path.** -/
theorem b3Rest2_arc_degree [T2Space C] (hE : Module.finrank ℂ E = 1) (x : C) {P δ : ℝ → C}
    (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P) (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ)
    {a b s₀ s₁ : ℝ} (hab : a ≤ b) (hs : s₀ ≤ s₁)
    (hsrc : ∀ t ∈ Icc a b, P t ∈ (chartAt E x).source)
    (hendP : ∀ s, δ s ≠ P a ∧ δ s ≠ P b) (hendδ : ∀ t, P t ≠ δ s₀ ∧ P t ≠ δ s₁)
    (hfin : {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc s₀ s₁ ∧ P p.1 = δ p.2}.Finite)
    (htr : ∀ t s, P t = δ s → b3_orient E (b3_velocity E C P t) (b3_velocity E C δ s) ≠ 0) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      b3Forms_lineIntegral (b3Rest_arcForm hE x ε (b3Rest2_arcC hE x P a b)
        (b3Rest2_arcC' hE x P a b) a b) δ s₀ s₁ =
      (∫ z, b3Rest_rho ε z) *
        ∑ᶠ p ∈ {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc s₀ s₁ ∧ P p.1 = δ p.2},
          (SignType.sign (b3_orient E (b3_velocity E C P p.1) (b3_velocity E C δ p.2)) : ℝ) := by
  set c := b3Rest2_arcC hE x P a b
  set c' := b3Rest2_arcC' hE x P a b
  set Y := {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc s₀ s₁ ∧ P p.1 = δ p.2}
  have hc : Continuous c := b3Rest2_continuous_arcC hE x hP hab hsrc
  have hc' : Continuous c' := b3Rest2_continuous_arcC' hE x hP hab hsrc
  have hcd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t := fun t ht ↦
    b3Rest2_hasDerivAt_arcC hE x hP hab hsrc ht
  set O := δ ⁻¹' (chartAt E x).source
  have hO : IsOpen O := b3Forms_isOpen_preimage_source hδ x
  set d : ℝ → ℂ := fun s ↦ b3Rest_pt hE x (δ s)
  set d' : ℝ → ℂ := fun s ↦ (b3Rest_L hE).symm (deriv (chartAt E x ∘ δ) s)
  have hd : ∀ s ∈ O, HasDerivAt d (d' s) s := fun s hs ↦ b3Rest2_hasDerivAt_pt hE x hδ hs
  have hd' : ContinuousOn d' O :=
    (b3Rest_L hE).symm.continuous.comp_continuousOn
      ((b3Forms_contDiffOn_chart_comp hδ x).continuousOn_deriv_of_isOpen hO le_rfl)
  -- a thickening of the arc inside the chart image
  have hcK : IsCompact (c '' Icc a b) := isCompact_Icc.image hc
  have hζ := b3Rest_continuous_ζ hE x
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := hcK.exists_cthickening_subset_open
    ((chartAt E x).open_target.preimage hζ) (by
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_preimage, show c t = b3Rest_pt hE x (P t) from b3Rest2_arcC_of_mem hE x ht,
        b3Rest_ζ_pt]
      exact (chartAt E x).map_source (hsrc t ht))
  set S := cthickening ε₀ (c '' Icc a b)
  have hSK : IsCompact S := hcK.cthickening
  set A := (chartAt E x).symm '' (b3Rest_ζ hE x '' S)
  have hAK : IsCompact A := (hSK.image hζ).image_of_continuousOn
    ((chartAt E x).continuousOn_symm.mono (by rintro _ ⟨z, hz, rfl⟩; exact hε₀sub hz))
  set Tc := Icc s₀ s₁ ∩ δ ⁻¹' A
  have hTc : IsCompact Tc := isCompact_Icc.inter_right (hAK.isClosed.preimage hδ.continuous)
  have hTcO : Tc ⊆ O := by
    rintro s ⟨-, u, ⟨z, hz, rfl⟩, hu⟩
    show δ s ∈ (chartAt E x).source
    rw [← hu]
    exact (chartAt E x).map_target (hε₀sub hz)
  have hTcI : Tc ⊆ Icc s₀ s₁ := inter_subset_left
  have hmemA : ∀ s ∈ O, d s ∈ S → δ s ∈ A := fun s hs hdS ↦
    ⟨chartAt E x (δ s), ⟨d s, hdS, b3Rest_ζ_pt hE x (δ s)⟩, (chartAt E x).left_inv hs⟩
  have haway : ∀ s ∈ Icc s₀ s₁, s ∈ O → s ∉ Tc → ∀ t ∈ Icc a b, ε₀ ≤ ‖d s - c t‖ := by
    intro s hs hsO hsT t ht
    by_contra hlt
    push_neg at hlt
    apply hsT
    refine ⟨hs, hmemA s hsO ?_⟩
    exact mem_cthickening_of_dist_le _ (c t) _ _ ⟨t, ht, rfl⟩
      (by rw [dist_eq_norm]; exact hlt.le)
  -- the crossings in complex form
  set Z := {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b ∧ d q.re = c q.im}
  have hZY : Z = (fun p : ℝ × ℝ ↦ (⟨p.2, p.1⟩ : ℂ)) '' Y := by
    ext q
    constructor
    · rintro ⟨hqT, hqI, hdc⟩
      refine ⟨(q.im, q.re), ⟨hqI, hTcI hqT, ?_⟩, Complex.ext rfl rfl⟩
      have hct : c q.im = b3Rest_pt hE x (P q.im) := b3Rest2_arcC_of_mem hE x hqI
      exact (b3Rest2_pt_injOn hE x (hsrc _ hqI) (hTcO hqT) (hct.symm.trans hdc.symm))
    · rintro ⟨p, ⟨hp1, hp2, hPδ⟩, rfl⟩
      have hct : c p.1 = b3Rest_pt hE x (P p.1) := b3Rest2_arcC_of_mem hE x hp1
      have hsO : p.2 ∈ O := by
        simp only [O, mem_preimage]; rw [← hPδ]; exact hsrc _ hp1
      refine ⟨⟨hp2, hmemA p.2 hsO ?_⟩, hp1, ?_⟩
      · show b3Rest_pt hE x (δ p.2) ∈ S
        rw [← hPδ, ← hct]
        exact self_subset_cthickening _ ⟨p.1, hp1, rfl⟩
      · show b3Rest_pt hE x (δ p.2) = c p.1
        rw [hct, hPδ]
  have hinjg : Function.Injective (fun p : ℝ × ℝ ↦ (⟨p.2, p.1⟩ : ℂ)) := by
    intro p p' h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    exact Prod.ext h2 h1
  have hZ : Z.Finite := by rw [hZY]; exact hfin.image _
  have hZint : ∀ q ∈ Z, q.re ∈ Ioo s₀ s₁ ∧ q.im ∈ Ioo a b := by
    intro q hq
    rw [hZY] at hq
    obtain ⟨p, ⟨hp1, hp2, hPδ⟩, rfl⟩ := hq
    refine ⟨⟨lt_of_le_of_ne hp2.1 ?_, lt_of_le_of_ne hp2.2 ?_⟩,
      ⟨lt_of_le_of_ne hp1.1 ?_, lt_of_le_of_ne hp1.2 ?_⟩⟩
    · intro h; exact (hendδ p.1).1 (by rw [hPδ]; exact congrArg δ h.symm)
    · intro h; exact (hendδ p.1).2 (by rw [hPδ]; exact congrArg δ h)
    · intro h; exact (hendP p.2).1 (by rw [← hPδ]; exact congrArg P h.symm)
    · intro h; exact (hendP p.2).2 (by rw [← hPδ]; exact congrArg P h)
  have hsign : ∀ p ∈ Y, SignType.sign ((conj (c' p.1) * d' p.2).im) =
      SignType.sign (b3_orient E (b3_velocity E C P p.1) (b3_velocity E C δ p.2)) := by
    rintro p ⟨hp1, hp2, hPδ⟩
    have hc'p : c' p.1 = (b3Rest_L hE).symm (deriv (chartAt E x ∘ P) p.1) := by
      simp only [c', b3Rest2_arcC', b3Rest2_clamp_of_mem hp1]
    rw [hc'p]
    exact b3Rest2_sign_orient hE hP hδ hPδ (hsrc _ hp1)
  have hZtr : ∀ q ∈ Z, (conj (c' q.im) * d' q.re).im ≠ 0 := by
    intro q hq
    rw [hZY] at hq
    obtain ⟨p, hpY, rfl⟩ := hq
    have := hsign p hpY
    intro h0
    rw [show (conj (c' p.1) * d' p.2).im = 0 from h0, sign_zero] at this
    exact htr _ _ hpY.2.2 (sign_eq_zero_iff.1 this.symm)
  obtain ⟨ε₁, hε₁, hdeg⟩ := b3Rest2_degree hab hs hO hTc hTcO hTcI hd hd' hc hc' hcd hε₀ haway
    hZ hZint hZtr
  refine ⟨ε₁, hε₁, fun ε hε hεlt ↦ ?_⟩
  have h1 := hdeg ε hε hεlt
  change _ = _ * ∑ᶠ q ∈ Z, _ at h1
  have hlhs : b3Forms_lineIntegral (b3Rest_arcForm hE x ε c c' a b) δ s₀ s₁ =
      ∫ s in s₀..s₁, O.indicator (fun s ↦ (conj (b3Rest_arcK ε c c' a b (d s)) * d' s).im) s := by
    unfold b3Forms_lineIntegral
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    exact b3Rest2_apply_arcForm hE x ε c c' a b hδ s
  rw [hlhs, h1, hZY, finsum_mem_image hinjg.injOn]
  congr 1
  refine finsum_mem_congr rfl fun p hp ↦ ?_
  simp only
  rw [hsign p hp]

theorem b3Rest2_periodic_fract {α : Type*} {f : ℝ → α} (hf : Function.Periodic f 1) (u : ℝ) :
    f (Int.fract u) = f u := by
  rw [Int.fract, show u - (⌊u⌋ : ℝ) = u - (⌊u⌋ : ℤ) * 1 by ring]
  exact hf.sub_int_mul_eq ⌊u⌋

theorem b3Rest2_fract_injOn (u c : ℝ) :
    InjOn (fun t ↦ Int.fract (t + c)) (Ico u (u + 1)) := by
  intro t ht t' ht' h
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 h
  have h1 : (z : ℝ) < 1 := by rw [← hz]; linarith [ht.1, ht.2, ht'.1, ht'.2]
  have h2 : (-1 : ℝ) < z := by rw [← hz]; linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hz0 : z = 0 := by
    have : z < 1 := by exact_mod_cast h1
    have : -1 < z := by exact_mod_cast h2
    omega
  rw [hz0, Int.cast_zero] at hz
  linarith

theorem b3Rest2_lineIntegral_sum {ι : Type*} (S : Finset ι) {β : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hβ : ∀ i ∈ S, b3Forms_IsSmooth (β i)) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a b : ℝ) :
    b3Forms_lineIntegral (∑ i ∈ S, β i) γ a b = ∑ i ∈ S, b3Forms_lineIntegral (β i) γ a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold b3Forms_lineIntegral
    simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      b3Forms_lineIntegral_add (hβ j (Finset.mem_insert_self j S))
        ((b3Forms_Ω E C 1).sum_mem fun i hi ↦ hβ i (Finset.mem_insert_of_mem hi)) hγ,
      ih fun i hi ↦ hβ i (Finset.mem_insert_of_mem hi)]

set_option maxHeartbeats 400000 in
/-- **Dual forms compute intersection numbers**: for transverse loops `γ`, `δ` there is a dual
form `η` of `γ` with `∫_δ η = γ · δ`. -/
theorem b3Rest2_key [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]
    (hE : Module.finrank ℂ E = 1) : b3Rest2_Key (C := C) hE := by
  intro γ δ htr
  have hZc := b3A_crossings_finite γ δ htr
  set Zc := b3_crossings E γ δ
  -- a shift with no rational differences to the crossing parameters
  set Bad : Set ℝ := ⋃ p ∈ Zc, Set.range (fun q : ℚ ↦ p.1 - (q : ℝ))
  have hBad : Bad.Countable := hZc.countable.biUnion fun p _ ↦ Set.countable_range _
  obtain ⟨a, ha⟩ := (hBad.dense_compl ℝ).nonempty
  have ha' : ∀ p ∈ Zc, ∀ q : ℚ, p.1 - (q : ℝ) ≠ a := fun p hp q h ↦
    ha (mem_biUnion hp ⟨q, h⟩)
  have hcross : ∀ t s, γ.1 t = δ.1 s → (Int.fract t, Int.fract s) ∈ Zc := fun t s h ↦
    ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, by
      simp only
      rw [b3Rest2_periodic_fract γ.2.1, b3Rest2_periodic_fract δ.2.1]
      exact h⟩
  -- the shifted loop and its chart cover
  set P : ℝ → C := fun t ↦ γ.1 (t + a)
  have hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P := b3Rest2_contMDiff_shift γ.2.2 a
  have hPper : Function.Periodic P 1 := fun t ↦ by
    simp only [P]; rw [add_right_comm]; exact γ.2.1 _
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b3Rest_exists_chartCover (E := E) P hP.continuous hPper
  let K : b3Rest_Cover E P := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  have hNpos : (0 : ℝ) < K.N := Nat.cast_pos.2 K.pos
  set D := range δ.1
  have hDc : IsClosed D := by
    show IsClosed (range δ.1)
    rw [← δ.2.1.image_Icc one_pos 0]
    exact (isCompact_Icc.image δ.2.2.continuous).isClosed
  have hw : ∀ k : ℤ, P (k / K.N) ∉ D := by
    rintro k ⟨s, hs⟩
    have := hcross _ _ hs.symm
    apply ha' _ this ((k : ℚ) / K.N - ⌊(k : ℝ) / K.N + a⌋)
    simp only [Int.fract]
    push_cast
    ring
  -- a base point of `δ` off `γ`
  obtain ⟨s₀, ⟨hs₀1, hs₀2⟩, hs₀Z⟩ :=
    ((Set.Ioo_infinite (zero_lt_one' ℝ)).diff (hZc.image Prod.snd)).nonempty
  have hs₀ : ∀ t, γ.1 t ≠ δ.1 s₀ := fun t h ↦
    hs₀Z ⟨_, hcross t s₀ h, by simp [Int.fract_eq_self.2 ⟨hs₀1.le, hs₀2⟩]⟩
  have hs₀' : δ.1 (s₀ + 1) = δ.1 s₀ := δ.2.1 s₀
  -- the pieces of the crossing set
  set Y : ℕ → Set (ℝ × ℝ) := fun i ↦ {p : ℝ × ℝ | p.1 ∈ Icc (((i : ℤ) : ℝ) / K.N)
    ((((i : ℤ) : ℝ) + 1) / K.N) ∧ p.2 ∈ Icc s₀ (s₀ + 1) ∧ P p.1 = δ.1 p.2}
  have hYnot : ∀ (k : ℤ) (p : ℝ × ℝ), P p.1 = δ.1 p.2 → p.1 ≠ (k : ℝ) / K.N := by
    intro k p h he
    exact hw k ⟨p.2, by rw [← h, he]⟩
  have hYnot' : ∀ p : ℝ × ℝ, P p.1 = δ.1 p.2 → p.2 ≠ s₀ + 1 := by
    intro p h he
    exact hs₀ (p.1 + a) (by rw [← hs₀', ← he]; exact h)
  have hYbox : ∀ i, Y i ⊆ Ico (((i : ℤ) : ℝ) / K.N) (((i : ℤ) : ℝ) / K.N + 1) ×ˢ Ico s₀ (s₀ + 1) := by
    rintro i p ⟨hp1, hp2, hPδ⟩
    have hlt : p.1 < ((((i : ℤ) : ℝ) + 1) / K.N) := lt_of_le_of_ne hp1.2 (by
      have := hYnot ((i : ℤ) + 1) p hPδ
      push_cast at this ⊢
      exact this)
    have hle : ((((i : ℤ) : ℝ) + 1) / K.N) ≤ ((i : ℤ) : ℝ) / K.N + 1 := by
      rw [add_div]
      have : (1 : ℝ) / K.N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast K.pos
      linarith
    exact ⟨⟨hp1.1, hlt.trans_le hle⟩, ⟨hp2.1, lt_of_le_of_ne hp2.2 (hYnot' p hPδ)⟩⟩
  set g : ℝ × ℝ → ℝ × ℝ := fun p ↦ (Int.fract (p.1 + a), Int.fract p.2)
  have hgZ : ∀ p : ℝ × ℝ, P p.1 = δ.1 p.2 → g p ∈ Zc := fun p h ↦ hcross _ _ h
  have hginj : ∀ u : ℝ, InjOn g (Ico u (u + 1) ×ˢ Ico s₀ (s₀ + 1)) := by
    intro u p hp p' hp' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Prod.ext (b3Rest2_fract_injOn u a hp.1 hp'.1 h1) ?_
    have := b3Rest2_fract_injOn s₀ 0 hp.2 hp'.2
    simp only [add_zero] at this
    exact this h2
  have hYfin : ∀ i, (Y i).Finite := fun i ↦
    Set.Finite.of_finite_image (hZc.subset (by rintro _ ⟨p, hp, rfl⟩; exact hgZ p hp.2.2))
      ((hginj _).mono (hYbox i))
  -- the degree of each arc
  have hdeg : ∀ i : ℕ, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      b3Forms_lineIntegral (b3Rest2_arcPiece hE K ε i) δ.1 s₀ (s₀ + 1) =
        (∫ z, b3Rest_rho ε z) * ∑ᶠ p ∈ Y i,
          (SignType.sign (b3_orient E (b3_velocity E C P p.1) (b3_velocity E C δ.1 p.2)) : ℝ) := by
    intro i
    refine b3Rest2_arc_degree hE (K.x i) hP δ.2.2 (b3Rest2_cover_le K) (by linarith)
      (fun t ht ↦ (b3Rest2_cover_mem K ht).1) (fun s ↦ ⟨fun h ↦ hw i ⟨s, h⟩, fun h ↦ ?_⟩)
      (fun t ↦ ⟨hs₀ (t + a), by rw [hs₀']; exact hs₀ (t + a)⟩) (hYfin i) ?_
    · apply hw ((i : ℤ) + 1)
      refine ⟨s, ?_⟩
      rw [h]
      push_cast
      rfl
    · intro t s h
      have := htr (t + a) s h
      rwa [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3, ← b3Rest2_velocity_shift γ.2.2 a t]
        at this
  choose ε₁ hε₁ hdeg' using hdeg
  obtain ⟨εm, hεm, hεmlt⟩ := b3Rest_exists_pos_lt (Finset.range K.N) ε₁ fun i _ ↦ hε₁ i
  obtain ⟨ε₀, hε₀, hdual⟩ := b3Rest2_exists_arcDual hE K hP hPper hDc hw
  set ε := min (ε₀ / 2) εm
  have hε : 0 < ε := lt_min (half_pos hε₀) hεm
  have hεε₀ : ε < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hε₀)
  have hεε₁ : ∀ i : Fin K.N, ε < ε₁ i := fun i ↦
    (min_le_right _ _).trans_lt (hεmlt i (Finset.mem_range.2 i.2))
  obtain ⟨κ, hσs, hκs, hκD, hηs, hηdual⟩ := hdual ε hε hεε₀
  set m := ∫ z, b3Rest_rho ε z
  have hm : 0 < m := b3Rest_integral_rho_pos hε
  refine ⟨m⁻¹ • ∑ i : Fin K.N, (b3Rest2_arcPiece hE K ε i + κ i), hηs,
    fun α hα hdα ↦ (hηdual α hα hdα).trans (b3Rest2_lineIntegral_shift α γ.2.2 γ.2.1 a), ?_⟩
  -- the integral along `δ`
  have hκ0 : ∀ i : Fin K.N, b3Forms_lineIntegral (κ i) δ.1 s₀ (s₀ + 1) = 0 := by
    intro i
    unfold b3Forms_lineIntegral
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s _ ↦ ?_).trans
      intervalIntegral.integral_zero
    have : κ i (δ.1 s) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hκD i _ h ⟨s, rfl⟩
    rw [this]
    rfl
  rw [← b3Rest2_lineIntegral_period _ δ.2.2 δ.2.1 s₀, b3Forms_lineIntegral_smul,
    b3Rest2_lineIntegral_sum _ (fun i _ ↦ (hσs i).add (hκs i)) δ.2.2]
  simp only [b3Forms_lineIntegral_add (hσs _) (hκs _) δ.2.2, hκ0, add_zero]
  rw [Finset.sum_congr rfl fun (i : Fin K.N) _ ↦ hdeg' (i : ℕ) ε hε (hεε₁ i), ← Finset.mul_sum,
    ← mul_assoc,
    inv_mul_cancel₀ hm.ne', one_mul]
  -- the pieces of crossings and the crossings of `γ` and `δ`
  set sg : ℝ × ℝ → ℝ := fun p ↦
    (SignType.sign (b3_orient E (b3_velocity E C γ.1 p.1) (b3_velocity E C δ.1 p.2)) : ℝ)
  have hI : (b3_intersection E γ δ : ℝ) = ∑ᶠ p ∈ Zc, sg p := by
    have h := (Int.castAddHom ℝ).map_finsum_mem (fun p : ℝ × ℝ ↦
      ((SignType.sign (b3_orient E (b3_velocity E C γ.1 p.1) (b3_velocity E C δ.1 p.2)) : ℤ)))
      hZc
    simp only [Int.coe_castAddHom] at h
    rw [b3_intersection, h]
    refine finsum_mem_congr rfl fun p _ ↦ ?_
    simp only [sg, SignType.intCast_cast]
  rw [hI, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ∑ᶠ p ∈ Y i,
    (SignType.sign (b3_orient E (b3_velocity E C P p.1) (b3_velocity E C δ.1 p.2)) : ℝ)) K.N,
    ← finsum_mem_coe_finset]
  have hdisj : (↑(Finset.range K.N) : Set ℕ).PairwiseDisjoint Y := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun p hpi hpj ↦ ?_
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : (((i : ℤ) : ℝ) + 1) / K.N ≤ ((j : ℤ) : ℝ) / K.N := by
        gcongr; exact_mod_cast h
      exact hYnot j p hpj.2.2 (le_antisymm (hpi.1.2.trans h1) hpj.1.1)
    · have h1 : (((j : ℤ) : ℝ) + 1) / K.N ≤ ((i : ℤ) : ℝ) / K.N := by
        gcongr; exact_mod_cast h
      exact hYnot i p hpi.2.2 (le_antisymm (hpj.1.2.trans h1) hpi.1.1)
  rw [← finsum_mem_biUnion hdisj (Finset.finite_toSet _) fun i _ ↦ hYfin i]
  refine finsum_mem_eq_of_bijOn g ⟨?_, ?_, ?_⟩ ?_
  · rintro p hp
    obtain ⟨i, -, hpi⟩ := mem_iUnion₂.1 hp
    exact hgZ p hpi.2.2
  · refine (hginj 0).mono fun p hp ↦ ?_
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 hp
    have hb := hYbox i hpi
    have hiN : i < K.N := Finset.mem_range.1 hi
    refine ⟨⟨?_, ?_⟩, hb.2⟩
    · exact le_trans (by positivity) hb.1.1
    · rw [zero_add]
      have h1 : p.1 ≤ (((i : ℤ) : ℝ) + 1) / K.N := hpi.1.2
      have h2 : (((i : ℤ) : ℝ) + 1) / K.N ≤ 1 := by
        rw [div_le_one hNpos]; push_cast; exact_mod_cast hiN
      refine lt_of_le_of_ne (h1.trans h2) fun he ↦ hYnot K.N p hpi.2.2 ?_
      rw [he]; push_cast; exact (div_self hNpos.ne').symm
  · rintro ⟨t', s'⟩ hp
    obtain ⟨⟨ht'0, ht'1⟩, ⟨hs'0, hs'1⟩, hγδ⟩ := hp
    set t := Int.fract (t' - a)
    set s := if s₀ ≤ s' then s' else s' + 1
    set i := (⌊(K.N : ℝ) * t⌋).toNat
    have ht0 : 0 ≤ t := Int.fract_nonneg _
    have ht1 : t < 1 := Int.fract_lt_one _
    have hfl0 : 0 ≤ ⌊(K.N : ℝ) * t⌋ := Int.floor_nonneg.2 (by positivity)
    have hi : ((i : ℤ) : ℝ) = (⌊(K.N : ℝ) * t⌋ : ℝ) := by
      simp only [i, Int.toNat_of_nonneg hfl0]
    have hPt : P t = γ.1 t' := by
      simp only [P, t]
      rw [Int.fract, show t' - a - (⌊t' - a⌋ : ℝ) + a = t' - (⌊t' - a⌋ : ℤ) * 1 by ring]
      exact γ.2.1.sub_int_mul_eq _
    have hδs : δ.1 s = δ.1 s' := by
      simp only [s]; split_ifs
      · rfl
      · exact δ.2.1 s'
    have hs0ne : s' ≠ s₀ := fun he ↦ hs₀Z ⟨(t', s'), ⟨⟨ht'0, ht'1⟩, ⟨hs'0, hs'1⟩, hγδ⟩, he⟩
    refine ⟨(t, s), mem_iUnion₂.2 ⟨i, Finset.mem_coe.2 (Finset.mem_range.2 ?_), ?_, ?_, ?_⟩, ?_⟩
    · have : ⌊(K.N : ℝ) * t⌋ < K.N := by
        rw [Int.floor_lt]; push_cast
        nlinarith
      omega
    · rw [hi]
      constructor
      · rw [div_le_iff₀ hNpos, mul_comm]; exact Int.floor_le _
      · rw [le_div_iff₀ hNpos, mul_comm]; exact (Int.lt_floor_add_one _).le
    · simp only [s]; split_ifs with h
      · exact ⟨h, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    · show P t = δ.1 s
      rw [hPt, hδs]; exact hγδ
    · simp only [g, t]
      refine Prod.ext ?_ ?_
      · simp only
        rw [show Int.fract (t' - a) + a = t' + ((-⌊t' - a⌋ : ℤ) : ℝ) by
          rw [Int.fract]; push_cast; ring, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨ht'0, ht'1⟩]
      · simp only [s]; split_ifs
        · exact Int.fract_eq_self.2 ⟨hs'0, hs'1⟩
        · rw [show s' + 1 = s' + ((1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast,
            Int.fract_eq_self.2 ⟨hs'0, hs'1⟩]
  · intro p hp
    simp only [sg, g]
    rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3,
      b3Forms_velocity_eq_b3, b3Rest2_velocity_shift γ.2.2 a p.1,
      show Int.fract (p.1 + a) = (p.1 + a) + ((-⌊p.1 + a⌋ : ℤ) : ℝ) by
        rw [Int.fract]; push_cast; ring,
      show Int.fract p.2 = p.2 + ((-⌊p.2⌋ : ℤ) : ℝ) by rw [Int.fract]; push_cast; ring,
      b3Rest2_velocity_add_int γ.2.2 γ.2.1, b3Rest2_velocity_add_int δ.2.2 δ.2.1]

end HodgeLean.Foundations.Program
