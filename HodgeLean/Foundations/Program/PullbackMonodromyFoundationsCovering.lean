import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsDescent

/-! # The degree-six covering and the index bound

Over `{z ≠ 0, 5, −7}` minus `1` and the critical values of the roots of `5s² − 3s + 4`,
`b65r_phi` is proper (it tends to `1` at infinity and to infinity at the poles), a local
homeomorphism (nonzero derivative) and has fibres of at most six points, so it is a covering map.
Filling the removed values is surjective on fundamental groups, so the image of the pulled-back
fundamental group has index at most six, also after a change of base point and a surjective
representation.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Bornology Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The finite set of values over which `b65r_phi` is not a covering: `1` and the critical values
of the roots of `5s² - 3s + 4`. -/
def b65t_S : Set ℂ := insert 1 (b65r_phi '' {s : ℂ | 5 * s ^ 2 - 3 * s + 4 = 0})

/-- The base of the degree-six covering. -/
def b65t_Bset : Set ℂ := {z | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7 ∧ z ∉ b65t_S}

/-- The total space of the degree-six covering. -/
def b65t_Eset : Set ℂ := b65r_phi ⁻¹' b65t_Bset

theorem b65t_S_finite : b65t_S.Finite := by
  have hq : {s : ℂ | 5 * s ^ 2 - 3 * s + 4 = 0}.Finite := by
    have hp : (C 5 * X ^ 2 - C 3 * X + C 4 : ℂ[X]) ≠ 0 := by
      intro h
      have := congrArg (eval 0) h
      norm_num at this
    have := Polynomial.finite_setOfPred_isRoot hp
    simpa [IsRoot] using this
  exact (hq.image _).insert 1

theorem b65t_Bset_open : IsOpen b65t_Bset := by
  have : b65t_Bset = ({0, 5, -7} ∪ b65t_S)ᶜ := by
    ext z
    simp only [b65t_Bset, mem_ofPred_eq, mem_compl_iff, mem_union, mem_insert_iff,
      mem_singleton_iff]
    tauto
  rw [this, isOpen_compl_iff]
  exact ((Set.toFinite _).union b65t_S_finite).isClosed

theorem b65t_Eset_sub : b65t_Eset ⊆ b65s_regular := by
  intro s hs
  obtain ⟨h0, h5, h7, -⟩ := hs
  have h1 : s ≠ 1 := by rintro rfl; apply h0; norm_num [b65r_phi]
  have h2 : s ≠ -2 := by rintro rfl; apply h0; norm_num [b65r_phi]
  have hD := b65t_den_ne h1 h2
  refine ⟨?_, ?_, h1, h2, ?_, ?_⟩
  · rintro rfl; apply h0; norm_num [b65r_phi]
  · rintro rfl; apply h0; norm_num [b65r_phi]
  · intro hP; apply h5
    unfold b65r_phi; rw [div_eq_iff hD]; unfold b65r_P at hP; linear_combination hP
  · intro hP; apply h7
    unfold b65r_phi; rw [div_eq_iff hD]; unfold b65r_P at hP; linear_combination hP

theorem b65t_Eset_open : IsOpen b65t_Eset := by
  have : b65t_Eset = b65s_regular ∩ b65r_phi ⁻¹' b65t_Bset := by
    ext s
    exact ⟨fun h ↦ ⟨b65t_Eset_sub h, h⟩, fun h ↦ h.2⟩
  rw [this]
  exact b65t_phi_analytic.continuousOn.isOpen_inter_preimage b65t_regular_open b65t_Bset_open

/-- Near a pole, `b65r_phi` is large. -/
theorem b65t_phi_pole (a : ℂ) (ha : a = 1 ∨ a = -2) (M : ℝ) :
    ∃ ε > 0, ∀ s : ℂ, 0 < ‖s - a‖ → ‖s - a‖ < ε → M < ‖b65r_phi s‖ := by
  let N : ℂ → ℂ := fun s ↦ s ^ 2 * (s - 3) ^ 4
  let D : ℂ → ℂ := fun s ↦ (s - 1) ^ 3 * (s + 2) ^ 3
  have hNa : N a ≠ 0 := by rcases ha with rfl | rfl <;> norm_num [N]
  have hDa : D a = 0 := by rcases ha with rfl | rfl <;> norm_num [D]
  have hNc : Continuous N := by fun_prop
  have hDc : Continuous D := by fun_prop
  set n := ‖N a‖ / 2 with hn
  have hn0 : 0 < n := by rw [hn]; exact half_pos (norm_pos_iff.mpr hNa)
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.continuous_iff.mp hNc a n hn0
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.continuous_iff.mp hDc a (n / M') (div_pos hn0 hM'0)
  refine ⟨min (min ε₁ ε₂) 1, by positivity, fun s hs0 hs ↦ ?_⟩
  have hs1 : dist s a < ε₁ := by rw [dist_eq_norm]; exact hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : dist s a < ε₂ := by rw [dist_eq_norm]; exact hs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : ‖s - a‖ < 1 := hs.trans_le (min_le_right _ _)
  have hNs : n < ‖N s‖ := by
    have := h₁ s hs1
    rw [dist_eq_norm] at this
    have := norm_sub_norm_le (N a) (N a - N s)
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at this
    linarith
  have hDs : ‖D s‖ < n / M' := by
    have := h₂ s hs2
    rwa [dist_eq_norm, hDa, sub_zero] at this
  have hsa : s ≠ a := fun h ↦ by rw [h, sub_self, norm_zero] at hs0; exact lt_irrefl _ hs0
  have hD0 : D s ≠ 0 := by
    have hs1' : s ≠ 1 := by
      rcases ha with rfl | rfl
      · exact hsa
      · rintro rfl; norm_num at hs3
    have hs2' : s ≠ -2 := by
      rcases ha with rfl | rfl
      · rintro rfl; norm_num at hs3
      · exact hsa
    exact b65t_den_ne hs1' hs2'
  have hφ : b65r_phi s = N s / D s := rfl
  rw [hφ, norm_div]
  have hDpos : 0 < ‖D s‖ := norm_pos_iff.mpr hD0
  rw [lt_div_iff₀ hDpos]
  calc M * ‖D s‖ ≤ M' * ‖D s‖ := by gcongr; exact le_max_left _ _
    _ < M' * (n / M') := by gcongr
    _ = n := by field_simp
    _ < ‖N s‖ := hNs


/-- The degree-six map over its base. -/
def b65t_pE : b65t_Eset → b65t_Bset := b65t_Bset.restrictPreimage b65r_phi

theorem b65t_pE_continuous : Continuous b65t_pE :=
  ((b65t_phi_analytic.continuousOn.mono b65t_Eset_sub).restrict).subtype_mk _

theorem b65t_deriv_ne {s : ℂ} (hs : s ∈ b65t_Eset) : deriv b65r_phi s ≠ 0 := by
  obtain ⟨h0, h3, h1, h2, -, -⟩ := b65t_Eset_sub hs
  rw [(b65t_phi_hasDerivAt s h1 h2).deriv]
  have hq : 5 * s ^ 2 - 3 * s + 4 ≠ 0 := by
    intro hq
    exact hs.2.2.2 (mem_insert_of_mem _ ⟨s, hq, rfl⟩)
  have h3' : s - 3 ≠ 0 := sub_ne_zero.mpr h3
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h2' : s + 2 ≠ 0 := fun h ↦ h2 (by linear_combination h)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h0) (pow_ne_zero _ h3')) hq)
    (mul_ne_zero (pow_ne_zero _ h1') (pow_ne_zero _ h2'))

theorem b65t_pE_localHomeo : IsLocalHomeomorph b65t_pE := by
  apply IsLocalHomeomorph.of_comp (g := (Subtype.val : b65t_Bset → ℂ)) _
    b65t_Bset_open.isOpenEmbedding_subtypeVal.isLocalHomeomorph b65t_pE_continuous
  apply IsLocalHomeomorph.mk
  intro x
  have hstrict : HasStrictDerivAt b65r_phi (deriv b65r_phi x) x :=
    (b65t_phi_analytic x (b65t_Eset_sub x.2)).hasStrictDerivAt
  let hF := hstrict.hasStrictFDerivAt_equiv (b65t_deriv_ne x.2)
  let e := hF.toOpenPartialHomeomorph b65r_phi
  let O : TopologicalSpace.Opens ℂ := ⟨b65t_Eset, b65t_Eset_open⟩
  refine ⟨e.subtypeRestr (s := O) ⟨x⟩, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hF.mem_toOpenPartialHomeomorph_source
  · intro y _
    change b65r_phi (y : ℂ) = e (y : ℂ)
    rw [show (e : ℂ → ℂ) = b65r_phi from hF.toOpenPartialHomeomorph_coe]

theorem b65t_pE_proper : IsProperMap b65t_pE := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨b65t_pE_continuous, fun K hK ↦ ?_⟩
  set Kc : Set ℂ := (Subtype.val : b65t_Bset → ℂ) '' K
  have hKc : IsCompact Kc := hK.image continuous_subtype_val
  have hKcB : Kc ⊆ b65t_Bset := by rintro _ ⟨k, -, rfl⟩; exact k.2
  have himg : (Subtype.val : b65t_Eset → ℂ) '' (b65t_pE ⁻¹' K) = {s | b65r_phi s ∈ Kc} := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨_, ht, rfl⟩
    · rintro ⟨k, hk, hks⟩
      have hsE : s ∈ b65t_Eset := by
        change b65r_phi s ∈ b65t_Bset
        rw [← hks]; exact k.2
      refine ⟨⟨s, hsE⟩, ?_, rfl⟩
      change b65t_pE ⟨s, hsE⟩ ∈ K
      have : b65t_pE ⟨s, hsE⟩ = k := Subtype.ext hks.symm
      rw [this]; exact hk
  rw [Subtype.isCompact_iff, himg]
  -- bounds
  have h1K : (1 : ℂ) ∉ Kc := fun h ↦ (hKcB h).2.2.2 (mem_insert _ _)
  have h0K : (0 : ℂ) ∉ Kc := fun h ↦ (hKcB h).1 rfl
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.mp hKc.isClosed.isOpen_compl 1 h1K
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (b65t_phi_tendsto.eventually (Metric.ball_mem_nhds 1 hδ))
  obtain ⟨M, hM⟩ := hKc.isBounded.exists_norm_le
  obtain ⟨ε₁, hε₁, hp₁⟩ := b65t_phi_pole 1 (Or.inl rfl) M
  obtain ⟨ε₂, hε₂, hp₂⟩ := b65t_phi_pole (-2) (Or.inr rfl) M
  set ε := min ε₁ ε₂
  let Q : Set ℂ := closedBall 0 R ∩ {s | ε ≤ ‖s - 1‖} ∩ {s | ε ≤ ‖s - -2‖}
  have hQc : IsCompact Q :=
    ((isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const (by fun_prop))).inter_right
      (isClosed_le continuous_const (by fun_prop))
  have hsub : {s | b65r_phi s ∈ Kc} ⊆ Q := by
    intro s hs
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      by_contra hlt
      push Not at hlt
      exact hδK (hR hlt.le) hs
    · by_contra hlt
      simp only [mem_ofPred_eq, not_le] at hlt
      by_cases hs1 : ‖s - 1‖ = 0
      · have : s = 1 := sub_eq_zero.mp (norm_eq_zero.mp hs1)
        subst this
        exact h0K (by simpa [b65r_phi] using hs)
      · have := hp₁ s (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs1))
          (hlt.trans_le (min_le_left _ _))
        linarith [hM _ hs]
    · by_contra hlt
      simp only [mem_ofPred_eq, not_le] at hlt
      by_cases hs1 : ‖s - -2‖ = 0
      · have : s = -2 := sub_eq_zero.mp (norm_eq_zero.mp hs1)
        subst this
        exact h0K (by norm_num [b65r_phi] at hs ⊢; exact hs)
      · have := hp₂ s (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs1))
          (hlt.trans_le (min_le_right _ _))
        linarith [hM _ hs]
  have hcont : ContinuousOn b65r_phi Q := by
    intro s hs
    have hε : 0 < ε := lt_min hε₁ hε₂
    have h1 : s ≠ 1 := by
      rintro rfl; have := hs.1.2; simp at this; linarith
    have h2 : s ≠ -2 := by
      rintro rfl; have := hs.2; simp at this; linarith
    apply ContinuousAt.continuousWithinAt
    unfold b65r_phi
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (b65t_den_ne h1 h2)
  have hcl : IsClosed (Q ∩ b65r_phi ⁻¹' Kc) :=
    hcont.preimage_isClosed_of_isClosed hQc.isClosed hKc.isClosed
  have heq : {s | b65r_phi s ∈ Kc} = Q ∩ b65r_phi ⁻¹' Kc := by
    ext s; exact ⟨fun h ↦ ⟨hsub h, h⟩, fun h ↦ h.2⟩
  rw [heq]
  exact hQc.of_isClosed_subset hcl inter_subset_left

theorem b65t_Ppoly_natDegree (ε : ℂ) : (b65t_Ppoly ε).natDegree ≤ 6 := by
  unfold b65t_Ppoly
  compute_degree

theorem b65t_fibre (b : b65t_Bset) :
    (b65t_pE ⁻¹' {b}).Finite ∧ Nat.card (b65t_pE ⁻¹' {b}) ≤ 6 := by
  classical
  let R := (b65t_Ppoly b).roots.toFinset
  have hmem : ∀ s : b65t_pE ⁻¹' {b}, (s.val.val : ℂ) ∈ R := by
    intro s
    have hφ : b65r_phi s.val.val = b := congrArg Subtype.val s.property
    obtain ⟨-, -, h1, h2, -, -⟩ := b65t_Eset_sub s.val.property
    have hD := b65t_den_ne h1 h2
    rw [Multiset.mem_toFinset, mem_roots (b65t_Ppoly_ne_zero _), IsRoot, b65t_Ppoly_eval]
    unfold b65r_phi at hφ
    rw [div_eq_iff hD] at hφ
    unfold b65r_P
    linear_combination hφ
  let f : b65t_pE ⁻¹' {b} → R := fun s ↦ ⟨s.val.val, hmem s⟩
  have hf : Function.Injective f := by
    intro s t h
    have h' := congrArg (fun r : R ↦ (r : ℂ)) h
    exact Subtype.ext (Subtype.ext h')
  have hfin : Finite (b65t_pE ⁻¹' {b}) := Finite.of_injective f hf
  refine ⟨Set.toFinite _, ?_⟩
  calc Nat.card (b65t_pE ⁻¹' {b}) ≤ Nat.card R := Nat.card_le_card_of_injective f hf
    _ = R.card := Nat.card_eq_finsetCard R
    _ ≤ (b65t_Ppoly b).roots.card := Multiset.toFinset_card_le _
    _ ≤ (b65t_Ppoly b).natDegree := card_roots' _
    _ ≤ 6 := b65t_Ppoly_natDegree _

theorem b65t_pE_covering : IsCoveringMap b65t_pE :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (b65t_pE_proper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun b _ ↦ (b65t_fibre b).1)
      ((isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp b65t_pE_localHomeo).mono
        (subset_univ _)))


open CategoryTheory in

theorem b65t_map_conj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x y : X} (p : Path x y) (c : FundamentalGroup X x) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath p c) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x c) := by
  have h := (FundamentalGroupoid.map f).map_conj ((Groupoid.isoEquivHom _ _).symm ⟦p⟧) c
  have hiso : (FundamentalGroupoid.map f).mapIso ((Groupoid.isoEquivHom _ _).symm ⟦p⟧) =
      (Groupoid.isoEquivHom _ _).symm ⟦p.map f.continuous⟧ := by
    ext; rfl
  rw [hiso] at h
  exact End.ext h

/-- The degree-six map as a continuous map to the four-point domain. -/
def b65t_phiC : C(b65s_regular, {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}) :=
  ⟨fun z ↦ ⟨b65r_phi z, b65t_phi_maps z.property⟩,
    (b65t_phi_analytic.continuousOn.restrict).subtype_mk _⟩

/-- The inclusion of the base of the covering into the four-point domain. -/
def b65t_j : C(b65t_Bset, {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}) :=
  ⟨fun b ↦ ⟨b.val, b.2.1, b.2.2.1, b.2.2.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of the total space of the covering into the regular domain. -/
def b65t_ιE : C(b65t_Eset, b65s_regular) :=
  ⟨fun s ↦ ⟨s.val, b65t_Eset_sub s.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem b65t_fromPath_rep {X : Type*} [TopologicalSpace X] {x : X} (c : FundamentalGroup X x) :
    ∃ γ : Path x x, c = FundamentalGroup.fromPath ⟦γ⟧ := by
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep c.asHom
  exact ⟨γ, by rw [show (⟦γ⟧ : Path.Homotopic.Quotient x x) = c.asHom from hγ]⟩

theorem b65t_square (s₀ : b65t_Eset) (c : FundamentalGroup b65t_Eset s₀) :
    FundamentalGroup.map b65t_phiC (b65t_ιE s₀) (FundamentalGroup.map b65t_ιE s₀ c) =
      FundamentalGroup.map b65t_j (b65t_pE s₀) (FundamentalGroup.map ⟨b65t_pE, b65t_pE_continuous⟩ s₀ c) := by
  obtain ⟨γ, rfl⟩ := b65t_fromPath_rep c
  rfl


/-- The four-point domain in the sphere. -/
def b65t_X4 : Set (OnePoint ℂ) := (fun z : ℂ ↦ (z : OnePoint ℂ)) '' {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}

open Classical in
/-- The values filled to pass from the covering base to the four-point domain. -/
def b65t_FS : Finset (OnePoint ℂ) := b65t_S_finite.toFinset.image (fun z : ℂ ↦ (z : OnePoint ℂ))

theorem b65t_X4_open : IsOpen b65t_X4 :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ b65t_four_open

theorem b65t_coe_X4 (z : ℂ) : (z : OnePoint ℂ) ∈ b65t_X4 ↔ (z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7) := by
  constructor
  · rintro ⟨w, hw, he⟩; rwa [← OnePoint.coe_injective he]
  · intro h; exact ⟨z, h, rfl⟩

theorem b65t_coe_XB (z : ℂ) :
    (z : OnePoint ℂ) ∈ b65t_X4 \ (b65t_FS : Set (OnePoint ℂ)) ↔ z ∈ b65t_Bset := by
  classical
  have hF : (z : OnePoint ℂ) ∈ (b65t_FS : Set (OnePoint ℂ)) ↔ z ∈ b65t_S := by
    simp only [b65t_FS, Finset.coe_image, mem_image, Finite.coe_toFinset]
    constructor
    · rintro ⟨w, hw, he⟩; rwa [← OnePoint.coe_injective he]
    · intro h; exact ⟨z, h, rfl⟩
  rw [Set.mem_sdiff, b65t_coe_X4, hF]
  simp only [b65t_Bset, mem_ofPred_eq]
  tauto

theorem b65t_X4_ne_infty (q : b65t_X4) : (q : OnePoint ℂ) ≠ OnePoint.infty := by
  obtain ⟨w, -, hw⟩ := q.property
  rw [← hw]; exact OnePoint.coe_ne_infty w

theorem b65t_X4_elim (q : b65t_X4) :
    ((q : OnePoint ℂ).elim 0 id ≠ 0 ∧ (q : OnePoint ℂ).elim 0 id ≠ 5 ∧
      (q : OnePoint ℂ).elim 0 id ≠ -7) ∧
      (((q : OnePoint ℂ).elim 0 id : ℂ) : OnePoint ℂ) = q := by
  obtain ⟨w, hw, he⟩ := q.property
  have h1 : (q : OnePoint ℂ).elim 0 id = w := by rw [← he]; rfl
  rw [h1]; exact ⟨hw, he⟩

theorem b65t_XB_elim (q : ↥(b65t_X4 \ (b65t_FS : Set (OnePoint ℂ)))) :
    (q : OnePoint ℂ).elim 0 id ∈ b65t_Bset ∧
      (((q : OnePoint ℂ).elim 0 id : ℂ) : OnePoint ℂ) = q := by
  have := b65t_X4_elim ⟨q.val, q.property.1⟩
  refine ⟨(b65t_coe_XB _).mp ?_, this.2⟩
  rw [this.2]; exact q.property

def b65t_chartU : C({z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}, b65t_X4) :=
  ⟨fun u ↦ ⟨(u.val : OnePoint ℂ), (b65t_coe_X4 u.val).mpr u.property⟩,
    (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _⟩

def b65t_chartB : C(b65t_Bset, ↥(b65t_X4 \ (b65t_FS : Set (OnePoint ℂ)))) :=
  ⟨fun b ↦ ⟨(b.val : OnePoint ℂ), (b65t_coe_XB b.val).mpr b.property⟩,
    (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _⟩

theorem b65t_chartU_embedding : Topology.IsEmbedding b65t_chartU :=
  (Topology.IsEmbedding.subtypeVal.of_comp_iff (f := b65t_chartU)).mp
    ((OnePoint.isOpenEmbedding_coe.isEmbedding).comp Topology.IsEmbedding.subtypeVal)

theorem b65t_chartB_embedding : Topology.IsEmbedding b65t_chartB :=
  (Topology.IsEmbedding.subtypeVal.of_comp_iff (f := b65t_chartB)).mp
    ((OnePoint.isOpenEmbedding_coe.isEmbedding).comp Topology.IsEmbedding.subtypeVal)

def b65t_unchartU : C(b65t_X4, {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}) :=
  ⟨fun q ↦ ⟨(q : OnePoint ℂ).elim 0 id, (b65t_X4_elim q).1⟩, by
    let h := b65t_chartU_embedding.toHomeomorphOfSurjective
      (fun q ↦ ⟨⟨_, (b65t_X4_elim q).1⟩, Subtype.ext (b65t_X4_elim q).2⟩)
    refine h.symm.continuous.congr fun q ↦ ?_
    apply b65t_chartU_embedding.injective
    change h (h.symm q) = _
    rw [h.apply_symm_apply]
    exact Subtype.ext (b65t_X4_elim q).2.symm⟩

def b65t_unchartB : C(↥(b65t_X4 \ (b65t_FS : Set (OnePoint ℂ))), b65t_Bset) :=
  ⟨fun q ↦ ⟨(q : OnePoint ℂ).elim 0 id, (b65t_XB_elim q).1⟩, by
    let h := b65t_chartB_embedding.toHomeomorphOfSurjective
      (fun q ↦ ⟨⟨_, (b65t_XB_elim q).1⟩, Subtype.ext (b65t_XB_elim q).2⟩)
    refine h.symm.continuous.congr fun q ↦ ?_
    apply b65t_chartB_embedding.injective
    change h (h.symm q) = _
    rw [h.apply_symm_apply]
    exact Subtype.ext (b65t_XB_elim q).2.symm⟩

/-- Filling the values of `b65t_S` is surjective on fundamental groups. -/
theorem b65t_j_surjective (hfill : b65t_FillProp) (b : b65t_Bset) :
    Function.Surjective (FundamentalGroup.map b65t_j b) := by
  intro c
  obtain ⟨hs, -, -⟩ := hfill b65t_X4 b65t_X4_open b65t_FS (b65t_chartB b)
  obtain ⟨d, hd⟩ := hs (FundamentalGroup.map b65t_chartU (b65t_j b) c)
  refine ⟨FundamentalGroup.map b65t_unchartB (b65t_chartB b) d, ?_⟩
  have h1 : FundamentalGroup.map b65t_j b (FundamentalGroup.map b65t_unchartB (b65t_chartB b) d) =
      FundamentalGroup.map b65t_unchartU _
        (FundamentalGroup.map (b65t_fill b65t_X4 b65t_FS) (b65t_chartB b) d) := by
    obtain ⟨γ, rfl⟩ := b65t_fromPath_rep d
    rfl
  rw [h1, hd]
  obtain ⟨γ, rfl⟩ := b65t_fromPath_rep c
  rfl


theorem b65t_Bset_nonempty : b65t_Bset.Nonempty := by
  have : b65t_Bset = ({0, 5, -7} ∪ b65t_S)ᶜ := by
    ext z
    simp only [b65t_Bset, mem_ofPred_eq, mem_compl_iff, mem_union, mem_insert_iff,
      mem_singleton_iff]
    tauto
  rw [this]
  exact ((Set.toFinite _).union b65t_S_finite).infinite_compl.nonempty

theorem b65t_phi_onto (b : ℂ) (hb : b ≠ 1) : ∃ s : ℂ, s ≠ 1 ∧ s ≠ -2 ∧ b65r_phi s = b := by
  have hdeg : 0 < degree (b65t_Ppoly b) := by
    by_contra hle
    push Not at hle
    obtain ⟨c, hc⟩ : ∃ c, b65t_Ppoly b = C c := ⟨_, eq_C_of_degree_le_zero hle⟩
    have h0 := b65t_Ppoly_eval b 0
    have h1 := b65t_Ppoly_eval b 1
    have h3 := b65t_Ppoly_eval b 3
    rw [hc, eval_C] at h0 h1 h3
    norm_num [b65r_P] at h0 h1 h3
    rw [h1] at h0 h3
    have hb2 : b = 2 := by linear_combination -h0 / 8
    rw [hb2] at h3
    norm_num at h3
  obtain ⟨s, hs⟩ := Complex.exists_root hdeg
  rw [IsRoot, b65t_Ppoly_eval] at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num [b65r_P] at hs
  have h2 : s ≠ -2 := by rintro rfl; norm_num [b65r_P] at hs
  refine ⟨s, h1, h2, ?_⟩
  unfold b65r_phi
  rw [div_eq_iff (b65t_den_ne h1 h2)]
  unfold b65r_P at hs
  linear_combination hs

/-- The image of the pulled-back fundamental group has index at most six in the four-point group,
and so does its image under a surjective representation. -/
theorem b65t_index_bound (hfill : b65t_FillProp) (x : b65s_regular)
    (ρ₀ : FundamentalGroup {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} (b65t_phiC x) →* b4b_Group)
    (hsurj : Function.Surjective ρ₀) :
    (ρ₀.comp (FundamentalGroup.map b65t_phiC x)).range.index ≤ 6 := by
  obtain ⟨b, hb⟩ := b65t_Bset_nonempty
  obtain ⟨s₀, -, -, hs₀⟩ := b65t_phi_onto b (fun h ↦ hb.2.2.2 (by rw [h]; exact mem_insert _ _))
  let e : b65t_Eset := ⟨s₀, show b65r_phi s₀ ∈ b65t_Bset by rw [hs₀]; exact hb⟩
  let pEc : C(b65t_Eset, b65t_Bset) := ⟨b65t_pE, b65t_pE_continuous⟩
  have hcov := b65t_covering_index_proof b65t_pE b65t_pE_covering e (b65t_fibre _).1
  set H := (FundamentalGroup.map pEc e).range
  have hH0 : H.index ≠ 0 := hcov.1.ne'
  have hH6 : H.index ≤ 6 := hcov.2.trans (b65t_fibre _).2
  have hK : H.map (FundamentalGroup.map b65t_j (b65t_pE e)) ≤
      (FundamentalGroup.map b65t_phiC (b65t_ιE e)).range := by
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨_, b65t_square e c⟩
  have hdvd : (FundamentalGroup.map b65t_phiC (b65t_ιE e)).range.index ∣ H.index :=
    (Subgroup.index_dvd_of_le hK).trans (Subgroup.index_map_dvd _ (b65t_j_surjective hfill _))
  have he6 : (FundamentalGroup.map b65t_phiC (b65t_ιE e)).range.index ≤ 6 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hH0) hdvd).trans hH6
  have he0 : (FundamentalGroup.map b65t_phiC (b65t_ιE e)).range.index ≠ 0 :=
    fun h ↦ hH0 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  -- change of base point
  have : PathConnectedSpace b65s_regular :=
    isPathConnected_iff_pathConnectedSpace.mp b65t_regular_pathConnected
  let δ : Path x (b65t_ιE e) := PathConnectedSpace.somePath _ _
  let isoR := FundamentalGroup.fundamentalGroupMulEquivOfPath δ
  let isoU := FundamentalGroup.fundamentalGroupMulEquivOfPath (δ.map b65t_phiC.continuous)
  have hrange : (FundamentalGroup.map b65t_phiC (b65t_ιE e)).range =
      (FundamentalGroup.map b65t_phiC x).range.map (isoU : _ →* _) := by
    ext c
    constructor
    · rintro ⟨c', rfl⟩
      refine ⟨FundamentalGroup.map b65t_phiC x (isoR.symm c'), ⟨_, rfl⟩, ?_⟩
      change isoU _ = _
      rw [← b65t_map_conj]
      change FundamentalGroup.map b65t_phiC _ (isoR (isoR.symm c')) = _
      rw [MulEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨c', rfl⟩, rfl⟩
      exact ⟨isoR c', b65t_map_conj _ δ c'⟩
  have hx : (FundamentalGroup.map b65t_phiC x).range.index =
      (FundamentalGroup.map b65t_phiC (b65t_ιE e)).range.index := by
    rw [hrange, Subgroup.index_map_equiv]
  rw [MonoidHom.range_comp]
  have hd := Subgroup.index_map_dvd ((FundamentalGroup.map b65t_phiC x).range) hsurj
  rw [hx] at hd
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hd).trans he6

end HodgeLean.Foundations.Program