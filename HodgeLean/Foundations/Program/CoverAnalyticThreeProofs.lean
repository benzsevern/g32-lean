import HodgeLean.Foundations.Program.CoverAnalyticThreeDefs

/-! # The cover dictionary, stage 3: all-loop transfer (auxiliaries)

One auxiliary per statement of `CoverAnalyticThree.lean`. Statements 1–2 are general facts about
quotient covering maps (Mathlib only); statements 3–7 concern the cover family and the 5c
record. Statement 7 uses statements 5 and 6. Statement 3 restricts the atlas cover (moved by
`b6t_cover`) to the regular locus with statement 1; statement 4 compares residues of the
record's coefficient with those of `b65r_pullback`; statement 5 uses statements 1–4 with the
atlas embedding and the locality of transport (`b65g_transport_congr`); statement 6 pushes each
loop off small discs about the poles (`b65g_push_off`), applies
`b65p_schlesinger_isomonodromic`, and compares the deck monodromies at `θ` and at `0` in the
atlas cover through the free homotopy `θ' ↦ b6t_sphere⁻¹ ∘ b65p_mobius` along the segment
(`b65g_monodromy_free_homotopy`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Manifold Polynomial
open scoped Topology ContDiff unitInterval
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem caf_isQuotientCoveringMap_of_isOpenEmbedding_aux {E X E' X' G : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E'] [TopologicalSpace X']
    [Group G] [MulAction G E] [MulAction G E'] {p : E → X} {p' : E' → X'}
    (hp : IsQuotientCoveringMap p G) (Φ : E' → E) (ψ : X' → X)
    (hΦ : Topology.IsOpenEmbedding Φ) (hψ : Topology.IsOpenEmbedding ψ)
    (hequiv : ∀ (h : G) (e : E'), Φ (h • e) = h • Φ e)
    (hcomm : ∀ e, p (Φ e) = ψ (p' e)) (hrange : Set.range Φ = p ⁻¹' Set.range ψ) :
    IsQuotientCoveringMap p' G := by
  have hcont : Continuous p' := by
    rw [hψ.isInducing.continuous_iff]
    have : ψ ∘ p' = p ∘ Φ := funext fun e ↦ (hcomm e).symm
    rw [this]
    exact hp.continuous.comp hΦ.continuous
  have hsurj : Function.Surjective p' := by
    intro y
    obtain ⟨e, he⟩ := hp.surjective (ψ y)
    have : e ∈ Set.range Φ := by rw [hrange]; exact ⟨y, he.symm⟩
    obtain ⟨e', rfl⟩ := this
    exact ⟨e', hψ.injective ((hcomm e').symm.trans he)⟩
  have hopen : IsOpenMap p' := by
    intro W hW
    have h1 : IsOpen (p '' (Φ '' W)) := hp.isOpenQuotientMap.isOpenMap _ (hΦ.isOpenMap _ hW)
    have h2 : p' '' W = ψ ⁻¹' (p '' (Φ '' W)) := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨Φ w, ⟨w, hw, rfl⟩, hcomm w⟩
      · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
        exact ⟨w, hw, hψ.injective ((hcomm w).symm.trans h)⟩
    rw [h2]
    exact h1.preimage hψ.continuous
  have hq : Topology.IsQuotientMap p' := (IsOpenQuotientMap.mk hsurj hcont hopen).isQuotientMap
  refine (isQuotientCoveringMap_iff p' G).mpr ⟨hq, ⟨fun h ↦ ?_⟩, fun {e₁ e₂} ↦ ?_, fun e ↦ ?_⟩
  · rw [hΦ.isInducing.continuous_iff]
    have : Φ ∘ (fun e ↦ h • e) = (fun e ↦ h • e) ∘ Φ := funext fun e ↦ hequiv h e
    rw [this]
    exact (hp.continuous_const_smul h).comp hΦ.continuous
  · rw [← hψ.injective.eq_iff, ← hcomm, ← hcomm, hp.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, hΦ.injective ((hequiv g e₂).trans hg)⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, (hequiv g e₂).symm.trans (congrArg Φ hg)⟩
  · obtain ⟨U, hU, hUd⟩ := hp.disjoint (Φ e)
    refine ⟨Φ ⁻¹' U, hΦ.continuous.continuousAt.preimage_mem_nhds hU, fun g hg ↦ hUd g ?_⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, hga⟩ := hg
    exact ⟨Φ (g • a), ⟨Φ a, ha, (hequiv g a).symm⟩, hga⟩

theorem caf_fundamentalGroupToMulOpposite_map_aux {E X E' X' G : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E'] [TopologicalSpace X']
    [Group G] [MulAction G E] [MulAction G E'] {p : E → X} {p' : E' → X'}
    (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    (Φ : E' → E) (ψ : C(X', X)) (hΦ : Continuous Φ)
    (hequiv : ∀ (h : G) (e : E'), Φ (h • e) = h • Φ e)
    (hcomm : ∀ e, p (Φ e) = ψ (p' e)) {x' : X'} (e' : p' ⁻¹' {x'}) (e : p ⁻¹' {ψ x'})
    (he : (e : E) = Φ e') (γ : FundamentalGroup X' x') :
    hp'.fundamentalGroupToMulOpposite e' γ =
      hp.fundamentalGroupToMulOpposite e (FundamentalGroup.map ψ x' γ) := by
  obtain ⟨η, rfl⟩ : ∃ η : Path x' x', FundamentalGroup.fromPath ⟦η⟧ = γ := by
    obtain ⟨η, hη⟩ := Quotient.exists_rep γ.asHom
    exact ⟨η, by ext; exact hη⟩
  set g := (hp'.fundamentalGroupToMulOpposite e' (FundamentalGroup.fromPath ⟦η⟧)).unop with hg
  have h0 : η 0 = p' (e' : E') := by rw [η.source]; exact e'.2.symm
  let Γ' := hp'.isCoveringMap.liftPath η e' h0
  have hΓ'1 : Γ' 1 = g • (e' : E') := by
    have := hp'.unop_fundamentalGroupToMulOpposite_smul (e := e')
      (γ := FundamentalGroup.fromPath ⟦η⟧)
    rw [← hg] at this
    rw [this]
    exact (hp'.isCoveringMap.coe_monodromy_mk η e').symm
  let Γ : C(unitInterval, E) := ⟨Φ ∘ Γ', hΦ.comp Γ'.continuous⟩
  have key := hp.fundamentalGroupToMulOpposite_apply_mk_eq (e := e) (γ := η.map ψ.continuous)
    (g := g) (Γ := Γ) ?_ ?_ ?_
  · rw [← MulOpposite.op_unop (hp'.fundamentalGroupToMulOpposite e' _), ← hg]
    exact key.symm
  · funext s
    change p (Φ (Γ' s)) = ψ (η s)
    rw [hcomm]
    exact congrArg ψ (congrFun (hp'.isCoveringMap.liftPath_lifts η e' h0) s)
  · change Φ (Γ' 0) = e
    rw [hp'.isCoveringMap.liftPath_zero, he]
  · change Φ (Γ' 1) = g • (e : E)
    rw [hΓ'1, hequiv, he]

/-- The normalization inverts the `s`-coordinate at a finite point with finite `s`. -/
theorem b65g_mobius_sCoord (a b z : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hz : b - z * (b - a) ≠ 0) :
    b65p_mobius a b ((b65g_sCoord a b (z : OnePoint ℂ) : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hs : a * b / (b - z * (b - a)) ≠ 0 := div_ne_zero (mul_ne_zero ha hb) hz
  change b65p_mobius a b ((a * b / (b - z * (b - a)) : ℂ) : OnePoint ℂ) = _
  simp only [b65p_mobius, OnePoint.elim_some, hs, ite_false, b65s_normalize]
  congr 1
  field_simp
  ring

/-- The `s`-coordinate inverts the normalization at a finite nonzero `s`. -/
theorem b65g_sCoord_mobius (a b s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hs : s ≠ 0) :
    b65p_mobius a b (s : OnePoint ℂ) = ((b65s_normalize a b s : ℂ) : OnePoint ℂ) ∧
      b - b65s_normalize a b s * (b - a) ≠ 0 ∧
      b65g_sCoord a b ((b65s_normalize a b s : ℂ) : OnePoint ℂ) = s := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h : b - b65s_normalize a b s * (b - a) = a * b / s := by
    simp only [b65s_normalize]
    field_simp
    ring
  refine ⟨by simp [b65p_mobius, hs], by rw [h]; exact div_ne_zero (mul_ne_zero ha hb) hs, ?_⟩
  change a * b / (b - b65s_normalize a b s * (b - a)) = s
  rw [h]
  field_simp

/-- Each of the thirteen unnormalized branch points is one of the sixteen poles. -/
theorem b65g_source_mem (p : Fin 12 → ℂ) (θ : ℂ) (k : Fin 13) :
    ∃ q, b65p_source p θ k = ((b65p_poles p θ q : ℂ) : OnePoint ℂ) := by
  fin_cases k
  exacts [⟨Sum.inr 0, rfl⟩, ⟨Sum.inr 1, rfl⟩, ⟨Sum.inr 2, rfl⟩, ⟨Sum.inr 3, rfl⟩,
    ⟨Sum.inr 4, rfl⟩, ⟨Sum.inr 5, rfl⟩, ⟨Sum.inr 6, rfl⟩, ⟨Sum.inr 7, rfl⟩, ⟨Sum.inr 8, rfl⟩,
    ⟨Sum.inr 9, rfl⟩, ⟨Sum.inr 10, rfl⟩, ⟨Sum.inr 11, rfl⟩, ⟨Sum.inl 0, rfl⟩]

/-- **The regular locus is an open part of the atlas cover.** For a normalization `M` sending
the poles onto the branch points over `t`, and any map `P` of the atlas cover with values
`b6t_sphere c t ∘ f ∘ ι`, the regular locus embeds equivariantly and openly into the atlas cover
over the open embedding `s ↦ M s` of the base, onto the preimage of its image. -/
theorem b65g_regular_embedding {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (h0 : (0 : ℂ) ∈ Set.range poles)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ) (hM : ⇑M = b65p_mobius a b)
    (hbr : ∀ k, ∃ q, M (poles q : OnePoint ℂ) = b6_branch t.val k)
    (P : D.atlas.U → b6t_punctured t.val)
    (hP : ∀ u, (P u : OnePoint ℂ) = b6t_sphere c t.val (D.atlas.f (D.atlas.ι u))) :
    ∃ (Φ : b65g_goodSub D t a b poles → D.atlas.U) (ψ : b65g_U poles → b6t_punctured t.val),
      Topology.IsOpenEmbedding Φ ∧ Topology.IsOpenEmbedding ψ ∧
      (∀ (h : b4b_Group) v, Φ (h • v) = h • Φ v) ∧
      (∀ v, P (Φ v) = ψ (b65g_sProj D t a b poles v)) ∧
      Set.range Φ = P ⁻¹' Set.range ψ ∧
      (∀ s, (ψ s : OnePoint ℂ) = b65p_mobius a b (s.val : OnePoint ℂ)) ∧
      ∀ v, D.atlas.ι (Φ v) = v.val.val.2 := by
  classical
  set proj := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t with hproj_def
  have hproj : ∀ x : b65z_fibre c D.C t, proj x = b6t_sphere c t.val (D.atlas.f x.val.2) := by
    intro x
    show b6t_sphere c x.val.1.val (D.atlas.f x.val.2) = _
    rw [x.property]
  obtain ⟨E, hE⟩ := b6t_homeomorph c D.atlas.hb t.val t.property
  have hmarks := b6t_marks c D.atlas.hb t.val t.property
  have hfc : Continuous D.atlas.f := D.atlas.hf.continuous
  have hpc : Continuous proj := by
    have : proj = fun x : b65z_fibre c D.C t ↦ E (D.atlas.f x.val.2) := by
      funext x; rw [hproj, hE]
    rw [this]
    exact E.continuous.comp (hfc.comp (continuous_snd.comp continuous_subtype_val))
  have hUopen : IsOpen (b65g_U poles) := (Set.finite_range poles).isClosed.isOpen_compl
  set S : Set (OnePoint ℂ) := Set.range (fun s : b65g_U poles ↦ M (s.val : OnePoint ℂ))
    with hS
  have hSopen : IsOpen S := by
    have : S = M '' (((↑) : ℂ → OnePoint ℂ) '' b65g_U poles) := by
      ext w
      constructor
      · rintro ⟨s, rfl⟩; exact ⟨s.val, ⟨s.val, s.property, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨⟨s, hs⟩, rfl⟩
    rw [this]
    exact M.isOpenMap _ (OnePoint.isOpenEmbedding_coe.isOpenMap _ hUopen)
  have hs0 : ∀ s : b65g_U poles, s.val ≠ 0 := by
    rintro ⟨s, hs⟩ h
    obtain ⟨q, hq⟩ := h0
    exact hs ⟨q, hq.trans h.symm⟩
  have hgood : ∀ x : b65z_fibre c D.C t, x ∈ b65g_good D t a b poles ↔ proj x ∈ S := by
    intro x
    constructor
    · rintro ⟨z, hz, hw, hpole⟩
      refine ⟨⟨_, hpole⟩, ?_⟩
      change M _ = proj x
      rw [hM, b65g_mobius_sCoord a b z ha hb hab hw, ← hz]
    · rintro ⟨s, hs⟩
      obtain ⟨h1, h2, h3⟩ := b65g_sCoord_mobius a b s.val ha hb hab (hs0 s)
      refine ⟨b65s_normalize a b s.val, ?_, h2, ?_⟩
      · change proj x = _
        rw [← hs, ← h1]
        exact congrFun hM _
      · rw [h3]; exact s.property
  have hbranch : ∀ v : b65g_goodSub D t a b poles,
      D.atlas.f v.val.val.2 ∉ Set.range (b6_branch c) := by
    rintro v ⟨k, hk⟩
    obtain ⟨s, hs⟩ := (hgood v.val).mp v.property
    obtain ⟨q, hq⟩ := hbr k
    have h1 : proj v.val = b6_branch t.val k := by rw [hproj, ← hk, hmarks]
    have h2 : M (s.val : OnePoint ℂ) = M (poles q : OnePoint ℂ) := by
      change M (s.val : OnePoint ℂ) = proj v.val at hs
      rw [hs, h1, hq]
    exact s.property ⟨q, (OnePoint.coe_injective (M.injective h2)).symm⟩
  have hmem : ∀ v : b65g_goodSub D t a b poles, v.val.val.2 ∈ Set.range D.atlas.ι := by
    intro v
    rw [D.atlas.hrange]
    exact hbranch v
  let H := D.atlas.hι.isEmbedding.toHomeomorph
  let Φ : b65g_goodSub D t a b poles → D.atlas.U := fun v ↦ H.symm ⟨v.val.val.2, hmem v⟩
  have hΦι : ∀ v, D.atlas.ι (Φ v) = v.val.val.2 := by
    intro v
    show D.atlas.ι (H.symm _) = _
    rw [← Topology.IsEmbedding.toHomeomorph_apply_coe D.atlas.hι.isEmbedding, H.apply_symm_apply]
  have hψmem : ∀ s : b65g_U poles, M (s.val : OnePoint ℂ) ∈ b6t_punctured t.val := by
    rintro s ⟨k, hk⟩
    obtain ⟨q, hq⟩ := hbr k
    have h2 : M (s.val : OnePoint ℂ) = M (poles q : OnePoint ℂ) := by rw [← hk, hq]
    exact s.property ⟨q, (OnePoint.coe_injective (M.injective h2)).symm⟩
  let ψ : b65g_U poles → b6t_punctured t.val := fun s ↦ ⟨M s.val, hψmem s⟩
  have hgoodOpen : IsOpen (b65g_good D t a b poles) := by
    have : b65g_good D t a b poles = proj ⁻¹' S := by ext x; exact hgood x
    rw [this]
    exact hSopen.preimage hpc
  have hcomm : ∀ v, P (Φ v) = ψ (b65g_sProj D t a b poles v) := by
    intro v
    apply Subtype.ext
    change (P (Φ v) : OnePoint ℂ) = M (b65g_sFun D t a b v.val : OnePoint ℂ)
    obtain ⟨z, hz, hw, -⟩ := v.property
    rw [hP, hΦι, ← hproj v.val]
    show proj v.val = M (b65g_sCoord a b (proj v.val) : OnePoint ℂ)
    have hz' : proj v.val = (z : OnePoint ℂ) := hz
    rw [hz', hM, b65g_mobius_sCoord _ _ _ ha hb hab hw]
  refine ⟨Φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_, hΦι⟩
  · apply Topology.IsOpenEmbedding.of_comp Φ D.atlas.hι
    have : D.atlas.ι ∘ Φ = (b6m_coordinate c D.C t) ∘
        (Subtype.val : b65g_good D t a b poles → b65z_fibre c D.C t) := by
      funext v; exact hΦι v
    rw [this]
    exact (b6m_coordinate c D.C t).isOpenEmbedding.comp hgoodOpen.isOpenEmbedding_subtypeVal
  · have hPopen : IsOpen (b6t_punctured t.val) :=
      (Set.finite_range (b6_branch t.val)).isClosed.isOpen_compl
    apply Topology.IsOpenEmbedding.of_comp ψ hPopen.isOpenEmbedding_subtypeVal
    exact M.isOpenEmbedding.comp
      (OnePoint.isOpenEmbedding_coe.comp hUopen.isOpenEmbedding_subtypeVal)
  · intro h v
    apply D.atlas.hι.injective
    rw [D.atlas.hequiv, hΦι, hΦι]
    rfl
  · exact hcomm
  · ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, (hcomm v).symm⟩
    · rintro ⟨s, hs⟩
      let x : b65z_fibre c D.C t := ⟨(t, D.atlas.ι u), rfl⟩
      have hx : x ∈ b65g_good D t a b poles := by
        rw [hgood]
        refine ⟨s, ?_⟩
        change M (s.val : OnePoint ℂ) = proj x
        rw [hproj, ← hP]
        exact congrArg Subtype.val hs
      refine ⟨⟨x, hx⟩, D.atlas.hι.injective ?_⟩
      rw [hΦι]
  · intro s
    exact congrFun hM _

/-- The two moving poles used by the normalization are distinct and nonzero. -/
theorem b65g_moving_ne (p : Fin 12 → ℂ) (O : b65p_Outputs p) (θ : ℂ)
    (hθ : θ ∈ ball (0 : ℂ) O.radius) :
    b65p_moving p θ 10 ≠ 0 ∧ b65p_moving p θ 11 ≠ 0 ∧
      b65p_moving p θ 10 ≠ b65p_moving p θ 11 := by
  have hinj := O.poles_injective θ hθ
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact Sum.inr_ne_inl (hinj (a₁ := Sum.inr 10) (a₂ := Sum.inl 0) h)
  · exact Sum.inr_ne_inl (hinj (a₁ := Sum.inr 11) (a₂ := Sum.inl 0) h)
  · have := hinj (a₁ := Sum.inr 10) (a₂ := Sum.inr 11) h
    simp at this

/-- The normalization at `θ` sends the poles onto the branch points over `t`. -/
theorem b65g_branch_of_pole (p : Fin 12 → ℂ) (θ : ℂ) (t : Fin 10 → ℂ)
    (ht : t = b65p_curve p θ) (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ∀ k, M (b65p_source p θ k) = b6_branch (b65p_curve p θ) k) (k : Fin 13) :
    ∃ q, M ((b65p_poles p θ q : ℂ) : OnePoint ℂ) = b6_branch t k := by
  obtain ⟨q, hq⟩ := b65g_source_mem p θ k
  exact ⟨q, by rw [ht, ← hM k, hq]⟩

theorem b65g_quotientCovering_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) O.radius) (t : b6t_polydisc (b65z_centre p))
    (ht : t.val = b65p_curve p θ) :
    IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ)) b4b_Group := by
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθ
  obtain ⟨M, hM, hMk⟩ := O.normalization θ hθ
  obtain ⟨e, he, hcov, -⟩ := b6t_cover (b65z_centre p) D.atlas.hb t.val t.property b4b_Group
    D.atlas.U D.atlas.π D.atlas.hπ
  obtain ⟨Φ, ψ, hΦ, hψ, heq, hcomm, hrange, -, -⟩ := b65g_regular_embedding D t _ _ _ ha hb hab
    ⟨Sum.inl 0, rfl⟩ M hM (b65g_branch_of_pole p θ t.val ht M hMk) (e ∘ D.atlas.π)
    (fun u ↦ by rw [Function.comp_apply, he, ← D.atlas.hproj])
  exact caf_isQuotientCoveringMap_of_isOpenEmbedding_aux hcov Φ ψ hΦ hψ heq hcomm hrange

/-- **Logarithmic derivative of a polynomial.** For `Q ≠ 0`, `(z − r) Q'(z)/Q(z)` tends to the
multiplicity of `r` as `z → r`, and `Q` does not vanish near `r` off `r`. -/
theorem b65g_logDeriv_tendsto (Q : ℂ[X]) (hQ : Q ≠ 0) (r : ℂ) :
    Tendsto (fun z ↦ (z - r) * Q.derivative.eval z / Q.eval z) (𝓝[≠] r)
      (𝓝 (Q.rootMultiplicity r : ℂ)) ∧ ∀ᶠ z in 𝓝[≠] r, Q.eval z ≠ 0 := by
  obtain ⟨R, hQR, hR⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ r
  set m := Q.rootMultiplicity r
  have hRr : R.eval r ≠ 0 := by
    intro h; exact hR (Polynomial.dvd_iff_isRoot.mpr h)
  have hRev : ∀ᶠ z in 𝓝 r, R.eval z ≠ 0 :=
    R.continuous.continuousAt.eventually_ne hRr
  have hev : ∀ᶠ z in 𝓝[≠] r, R.eval z ≠ 0 ∧ z ≠ r :=
    (eventually_nhdsWithin_of_eventually_nhds hRev).and self_mem_nhdsWithin
  have hval : ∀ z, z ≠ r → R.eval z ≠ 0 →
      (z - r) * Q.derivative.eval z / Q.eval z =
        m + (z - r) * R.derivative.eval z / R.eval z := by
    intro z hz hRz
    have hzr : z - r ≠ 0 := sub_ne_zero.mpr hz
    rw [hQR, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
    have hpow : (z - r) * ((m : ℂ) * (z - r) ^ (m - 1)) = m * (z - r) ^ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h]; simp
      · rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel h]
    field_simp
    linear_combination R.eval z * hpow
  constructor
  · have hc : ContinuousAt (fun z ↦ (m : ℂ) + (z - r) * R.derivative.eval z / R.eval z) r :=
      (continuousAt_const.add (((continuousAt_id.sub continuousAt_const).mul
        R.derivative.continuous.continuousAt).div R.continuous.continuousAt hRr))
    have hlim : Tendsto (fun z ↦ (m : ℂ) + (z - r) * R.derivative.eval z / R.eval z) (𝓝[≠] r)
        (𝓝 m) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {r}ᶜ))
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [hev] with z hz
    exact (hval z hz.2 hz.1).symm
  · filter_upwards [hev] with z hz
    rw [hQR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz.2)) hz.1

/-- **Residues of an indexed Fuchsian coefficient.** `(z − r) Σ_q (z − t_q)⁻¹ A_q` tends to the
sum of the residues at the poles equal to `r`. -/
theorem b65g_coefficient_residue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) (r : ℂ) :
    Tendsto (fun z ↦ (z - r) • b65p_coefficient E t A z) (𝓝[≠] r)
      (𝓝 (∑ q, if t q = r then A q else 0)) := by
  classical
  simp only [b65p_coefficient, Finset.smul_sum]
  apply tendsto_finsetSum
  intro q _
  by_cases hq : t q = r
  · rw [ite_eq_left hq]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z - r ≠ 0 := sub_ne_zero.mpr hz
    rw [hq, smul_smul, mul_inv_cancel₀ hz', one_smul]
  · rw [ite_eq_right hq]
    have hne : r - t q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    have hc : ContinuousAt (fun z ↦ ((z - r) * (z - t q)⁻¹) • A q) r :=
      ((continuousAt_id.sub continuousAt_const).mul
        ((continuousAt_id.sub continuousAt_const).inv₀ hne)).smul continuousAt_const
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {r}ᶜ))
    simp only [sub_self, zero_mul, zero_smul] at this
    refine this.congr' (Eventually.of_forall fun z ↦ ?_)
    simp only [smul_smul]

/-- The polynomial `P_ε`. -/
def b65g_Ppoly (ε : ℂ) : ℂ[X] :=
  X ^ 2 * (X - C 3) ^ 4 - C ε * (X - C 1) ^ 3 * (X + C 2) ^ 3

theorem b65g_Ppoly_eval (ε z : ℂ) : (b65g_Ppoly ε).eval z = b65r_P ε z := by
  simp [b65g_Ppoly, b65r_P]

theorem b65g_Ppoly_ne_zero (ε : ℂ) (hε : ε ≠ 0) : b65g_Ppoly ε ≠ 0 := by
  intro h
  have := b65g_Ppoly_eval ε 0
  rw [h, Polynomial.eval_zero] at this
  norm_num [b65r_P] at this
  exact hε this

theorem b65g_deriv_P (ε z : ℂ) : deriv (b65r_P ε) z = (b65g_Ppoly ε).derivative.eval z := by
  have : b65r_P ε = fun z ↦ (b65g_Ppoly ε).eval z := funext fun z ↦ (b65g_Ppoly_eval ε z).symm
  rw [this, Polynomial.deriv]

/-- **Residue of the printed pullback** at a point other than `0, 3, 1, −2`: the multiplicities
of the point as a root of `P₅` and `P₋₇` times `B₅` and `B₋₇`. -/
theorem b65g_pullback_residue (r : ℂ) (h0 : r ≠ 0) (h3 : r ≠ 3) (h1 : r ≠ 1) (h2 : r ≠ -2) :
    Tendsto (fun z ↦ (z - r) • b65r_pullback z) (𝓝[≠] r)
      (𝓝 (((b65g_Ppoly 5).rootMultiplicity r : ℂ) • b65r_operator b65r_B5 +
        ((b65g_Ppoly (-7)).rootMultiplicity r : ℂ) • b65r_operator b65r_Bneg7)) := by
  have hrest : ∀ f : ℂ → ℂ, ContinuousAt f r →
      Tendsto (fun z ↦ (z - r) * f z) (𝓝[≠] r) (𝓝 0) := by
    intro f hf
    have hc : ContinuousAt (fun z ↦ (z - r) * f z) r :=
      (continuousAt_id.sub continuousAt_const).mul hf
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {r}ᶜ))
    simpa using this
  have hA := hrest (fun z ↦ 2 / z + 4 / (z - 3))
    ((continuousAt_const.div continuousAt_id h0).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr h3)))
  have hB := hrest (fun z ↦ 3 / (z - 1) + 3 / (z + 2))
    ((continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr h1)).add
      (continuousAt_const.div (continuousAt_id.add continuousAt_const)
        (by intro h; apply h2; linear_combination h)))
  have h5 := (b65g_logDeriv_tendsto (b65g_Ppoly 5) (b65g_Ppoly_ne_zero 5 (by norm_num)) r).1
  have h7 := (b65g_logDeriv_tendsto (b65g_Ppoly (-7)) (b65g_Ppoly_ne_zero (-7) (by norm_num)) r).1
  have hsum := (((hA.smul_const (b65r_operator b65r_B0)).add
    (h5.smul_const (b65r_operator b65r_B5))).add
      (h7.smul_const (b65r_operator b65r_Bneg7))).add (hB.smul_const (b65r_operator b65r_Binf))
  simp only [zero_smul, zero_add, add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun z ↦ ?_)
  simp only [b65r_pullback, smul_add, smul_smul, b65g_deriv_P, ← b65g_Ppoly_eval, mul_div_assoc]

theorem b65g_operator_B5_ne_zero : b65r_operator b65r_B5 ≠ 0 := by
  intro h
  have h' := congrArg (fun f : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ f (Pi.single 2 1) 0) h
  change (Matrix.mulVec b65r_B5 (Pi.single 2 1)) 0 =
    (0 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (Pi.single 2 1) 0 at h'
  rw [Matrix.mulVec_single_one] at h'
  norm_num [b65r_B5] at h'

theorem b65g_operator_Bneg7_ne_zero : b65r_operator b65r_Bneg7 ≠ 0 := by
  intro h
  have h' := congrArg (fun f : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ f (Pi.single 2 1) 2) h
  change (Matrix.mulVec b65r_Bneg7 (Pi.single 2 1)) 2 =
    (0 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (Pi.single 2 1) 2 at h'
  rw [Matrix.mulVec_single_one] at h'
  norm_num [b65r_Bneg7] at h'

/-- Near a point other than `0, 3, 1, −2`, every other point is in `b65s_regular`. -/
theorem b65g_eventually_regular (r : ℂ) (h0 : r ≠ 0) (h3 : r ≠ 3) (h1 : r ≠ 1)
    (h2 : r ≠ -2) : ∀ᶠ z in 𝓝[≠] r, z ∈ b65s_regular := by
  have e : ∀ c : ℂ, r ≠ c → ∀ᶠ z in 𝓝[≠] r, z ≠ c := fun c hc ↦
    eventually_nhdsWithin_of_eventually_nhds (continuousAt_id.eventually_ne hc)
  have h5 := (b65g_logDeriv_tendsto (b65g_Ppoly 5) (b65g_Ppoly_ne_zero 5 (by norm_num)) r).2
  have h7 := (b65g_logDeriv_tendsto (b65g_Ppoly (-7)) (b65g_Ppoly_ne_zero (-7) (by norm_num)) r).2
  filter_upwards [e 0 h0, e 3 h3, e 1 h1, e (-2) h2, h5, h7] with z a b c d f5 f7
  rw [b65g_Ppoly_eval] at f5 f7
  exact ⟨a, b, c, d, f5, f7⟩

theorem b65g_base_regular_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    b65g_U (b65p_poles p 0) = b65s_regular := by
  classical
  have hinj := O.poles_injective 0 (mem_ball_self O.radius_pos)
  have hfix : ∀ k, b65p_poles p 0 (Sum.inl k) = b65p_fixedPole k := fun _ ↦ rfl
  have hmov : ∀ j, b65p_poles p 0 (Sum.inr j) = p j := fun j ↦ by simp [b65p_poles]
  -- the residue of the record's coefficient equals that of `b65r_pullback` at every point
  -- other than `0, 3, 1, −2`
  have key : ∀ r : ℂ, r ≠ 0 → r ≠ 3 → r ≠ 1 → r ≠ -2 →
      (∑ q, if b65p_poles p 0 q = r then O.residue 0 q else 0) =
        ((b65g_Ppoly 5).rootMultiplicity r : ℂ) • b65r_operator b65r_B5 +
          ((b65g_Ppoly (-7)).rootMultiplicity r : ℂ) • b65r_operator b65r_Bneg7 := by
    intro r h0 h3 h1 h2
    refine tendsto_nhds_unique (b65g_coefficient_residue _ _ r) ?_
    refine (b65g_pullback_residue r h0 h3 h1 h2).congr' ?_
    filter_upwards [b65g_eventually_regular r h0 h3 h1 h2] with z hz
    rw [O.base_coefficient z hz]
  have hP5 : ∀ r, b65r_P 5 r = 0 → b65r_P (-7) r = 0 → r = 1 ∨ r = -2 := by
    intro r h5 h7
    have : 12 * ((r - 1) ^ 3 * (r + 2) ^ 3) = 0 := by
      simp only [b65r_P] at h5 h7
      linear_combination h7 - h5
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    rcases mul_eq_zero.mp h with h | h
    · left; linear_combination pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h
    · right; linear_combination pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h
  have hmult : ∀ ε : ℂ, ε ≠ 0 → ∀ r, ((b65g_Ppoly ε).rootMultiplicity r = 0 ↔ b65r_P ε r ≠ 0) := by
    intro ε hε r
    rw [Polynomial.rootMultiplicity_eq_zero_iff, Polynomial.IsRoot.def, b65g_Ppoly_eval]
    constructor
    · intro h h'; exact b65g_Ppoly_ne_zero ε hε (h h')
    · intro h h'; exact absurd h' h
  ext r
  constructor
  · intro hr
    have hne : ∀ q, b65p_poles p 0 q ≠ r := fun q h ↦ hr ⟨q, h⟩
    have h0 : r ≠ 0 := fun h ↦ hne (Sum.inl 0) (by rw [h]; rfl)
    have h3 : r ≠ 3 := fun h ↦ hne (Sum.inl 1) (by rw [h]; rfl)
    have h1 : r ≠ 1 := fun h ↦ hne (Sum.inl 2) (by rw [h]; rfl)
    have h2 : r ≠ -2 := fun h ↦ hne (Sum.inl 3) (by rw [h]; rfl)
    have hk := key r h0 h3 h1 h2
    simp only [hne, ite_false, Finset.sum_const_zero] at hk
    by_contra hreg
    have hroot : b65r_P 5 r = 0 ∨ b65r_P (-7) r = 0 := by
      by_contra h
      exact hreg ⟨h0, h3, h1, h2, fun h5 ↦ h (Or.inl h5), fun h7 ↦ h (Or.inr h7)⟩
    rcases hroot with h5 | h7
    · have h7 : b65r_P (-7) r ≠ 0 := fun h7 ↦ (hP5 r h5 h7).elim h1 h2
      rw [(hmult (-7) (by norm_num) r).mpr h7, Nat.cast_zero, zero_smul, add_zero] at hk
      have hpos : (b65g_Ppoly 5).rootMultiplicity r ≠ 0 := fun h ↦
        ((hmult 5 (by norm_num) r).mp h) h5
      rcases smul_eq_zero.mp hk.symm with h | h
      · exact hpos (by exact_mod_cast h)
      · exact b65g_operator_B5_ne_zero h
    · have h5 : b65r_P 5 r ≠ 0 := fun h5 ↦ (hP5 r h5 h7).elim h1 h2
      rw [(hmult 5 (by norm_num) r).mpr h5, Nat.cast_zero, zero_smul, zero_add] at hk
      have hpos : (b65g_Ppoly (-7)).rootMultiplicity r ≠ 0 := fun h ↦
        ((hmult (-7) (by norm_num) r).mp h) h7
      rcases smul_eq_zero.mp hk.symm with h | h
      · exact hpos (by exact_mod_cast h)
      · exact b65g_operator_Bneg7_ne_zero h
  · rintro hr ⟨q, hq⟩
    obtain ⟨h0, h3, h1, h2, h5, h7⟩ := hr
    rcases q with k | j
    · fin_cases k
      · exact h0 hq.symm
      · exact h3 hq.symm
      · exact h1 hq.symm
      · exact h2 hq.symm
    · have hk := key r h0 h3 h1 h2
      rw [(hmult 5 (by norm_num) r).mpr h5, (hmult (-7) (by norm_num) r).mpr h7] at hk
      simp only [Nat.cast_zero, zero_smul, add_zero] at hk
      have hiff : ∀ q, b65p_poles p 0 q = r ↔ q = Sum.inr j := fun q ↦
        ⟨fun h ↦ hinj (h.trans hq.symm), fun h ↦ h ▸ hq⟩
      simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hk
      rw [O.residue_zero] at hk
      simp only [b65p_initialResidue, Sum.elim_inr, b65p_movingResidue] at hk
      split_ifs at hk
      · exact b65g_operator_B5_ne_zero hk
      · exact b65g_operator_Bneg7_ne_zero hk

/-- The successive integrals along a segment depend only on the coefficient on the segment. -/
theorem b65g_iterated_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A A' : ℂ → E →L[ℂ] E} {u v : ℂ}
    (h : ∀ q ∈ Icc (0 : ℝ) 1, A (u + (q : ℂ) * (v - u)) = A' (u + (q : ℂ) * (v - u))) :
    ∀ m, ∀ r ∈ Icc (0 : ℝ) 1, b65f_iterated E A u v m r = b65f_iterated E A' u v m r := by
  intro m
  induction m with
  | zero => intro r _; rfl
  | succ m ih =>
    intro r hr
    simp only [b65f_iterated]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hr.1] at hq
    have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans hr.2⟩
    simp only
    rw [h q hq', ih q hq']

/-- **Locality of transport.** Transport along a path depends only on the coefficient on an open
set containing the path. -/
theorem b65g_transport_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A A' : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U) (hAA : ∀ z ∈ U, A z = A' z)
    (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1)) (hm : MapsTo γ (Icc 0 1) U) :
    b65f_transport E A γ = b65f_transport E A' γ := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.image_of_continuousOn hc).exists_thickening_subset_open
    hU (image_subset_iff.mpr hm)
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) δ hδ
  have hlim : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have heq : b65f_polygon E A γ =ᶠ[atTop] b65f_polygon E A' γ := by
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
    simp only [b65f_polygon]
    congr 2
    congr 1
    funext i
    have hk : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hi0 : (i.val : ℝ) / (2 : ℝ) ^ N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hk).mpr (by exact_mod_cast i.isLt.le |>.trans (by simp))⟩
    have hi1 : ((i.val : ℝ) + 1) / (2 : ℝ) ^ N ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, (div_le_one hk).mpr ?_⟩
      have : i.val + 1 ≤ 2 ^ N := i.isLt
      exact_mod_cast this
    have hd : dist (((i.val : ℝ) + 1) / (2 : ℝ) ^ N) ((i.val : ℝ) / (2 : ℝ) ^ N) < ε := by
      rw [Real.dist_eq, div_sub_div_same, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      simpa only [one_div] using hN
    have hball : ball (γ ((i.val : ℝ) / (2 : ℝ) ^ N)) δ ⊆ U :=
      (ball_subset_thickening (mem_image_of_mem γ hi0) δ).trans hsub
    have hv : γ (((i.val : ℝ) + 1) / (2 : ℝ) ^ N) ∈ ball (γ ((i.val : ℝ) / (2 : ℝ) ^ N)) δ :=
      mem_ball.mpr (he _ hi1 _ hi0 hd)
    simp only [b65f_segment]
    congr 1
    funext m
    exact b65g_iterated_congr (fun q hq ↦ hAA _ (hball (b65f_segment_mem_ball hv hq))) m 1
      ⟨zero_le_one, le_rfl⟩
  unfold b65f_transport
  rw [limUnder, limUnder, Filter.map_congr heq]

theorem b65g_base_transfer_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p 0) :
    ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p 0 10) (b65p_moving p 0 11)
        (b65p_poles p 0)) b4b_Group,
      b65g_loopTransfer D t (b65p_moving p 0 10) (b65p_moving p 0 11) (b65p_poles p 0)
        (O.residue 0) hπ := by
  obtain rfl : t = b65z_s₀ (b65z_centre p) := Subtype.ext ht
  have hθ : (0 : ℂ) ∈ ball (0 : ℂ) O.radius := mem_ball_self O.radius_pos
  have hπ := b65g_quotientCovering_aux p O g D 0 hθ (b65z_s₀ _) rfl
  refine ⟨hπ, ?_⟩
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O 0 hθ
  obtain ⟨M, hM, hMk⟩ := O.normalization 0 hθ
  have hP : ∀ u, ((D.atlas.π u : OnePoint ℂ)) = b6t_sphere (b65z_centre p)
      (b65z_s₀ (b65z_centre p)).val (D.atlas.f (D.atlas.ι u)) := by
    intro u
    rw [show (b65z_s₀ (b65z_centre p)).val = b65z_centre p from rfl, b6t_identity,
      D.atlas.hproj]
    rfl
  obtain ⟨Φ, ψ, hΦ, hψ, heq, hcomm, hrange, hψv, -⟩ := b65g_regular_embedding D
    (b65z_s₀ _) _ _ _ ha hb hab ⟨Sum.inl 0, rfl⟩ M hM (b65g_branch_of_pole p 0 _ rfl M hMk)
    D.atlas.π hP
  have h10 : b65p_moving p 0 10 = p 10 := by simp [b65p_moving, b65p_poles]
  have h11 : b65p_moving p 0 11 = p 11 := by simp [b65p_moving, b65p_poles]
  have hU := b65g_base_regular_aux p O
  have hRopen : IsOpen b65s_regular := hU ▸ (Set.finite_range _).isClosed.isOpen_compl
  let x' : b65g_U (b65p_poles p 0) := ⟨x.val, hU.symm ▸ x.property⟩
  let ψ₂ : C(b65g_U (b65p_poles p 0), b6t_punctured (b65z_centre p)) :=
    ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp
      b65s_inclusion).comp ⟨Homeomorph.setCongr hU, (Homeomorph.setCongr hU).continuous⟩
  have hψ₂ : ∀ s, (ψ₂ s : OnePoint ℂ) = (ψ s : OnePoint ℂ) := by
    intro s
    rw [hψv, h10, h11]
    exact he _
  have hcomm₂ : ∀ v, D.atlas.π (Φ v) = ψ₂ (b65g_sProj D _ _ _ _ v) := by
    intro v
    apply Subtype.ext
    rw [hψ₂]
    exact congrArg Subtype.val (hcomm v)
  obtain ⟨v, hv⟩ : u₀.val ∈ Set.range Φ := by
    rw [hrange]
    refine ⟨x', Subtype.ext ?_⟩
    rw [← hψ₂]
    exact (congrArg Subtype.val u₀.property).symm
  have hvx : b65g_sProj D _ _ _ _ v = x' := by
    apply hψ.injective
    rw [← hcomm, hv]
    apply Subtype.ext
    rw [← hψ₂]
    exact congrArg Subtype.val u₀.property
  let u : b65g_sProj D _ _ _ _ ⁻¹' {x'} := ⟨v, hvx⟩
  refine ⟨x', u, C, fun η ↦ ?_⟩
  have hA := b65g_transport_congr (E := Fin 4 → ℂ) hRopen
    (fun z hz ↦ O.base_coefficient z hz) (fun r ↦ (η.extend r).val)
    (continuous_subtype_val.comp η.continuous_extend).continuousOn
    (fun r _ ↦ hU ▸ (η.extend r).property)
  have key := caf_fundamentalGroupToMulOpposite_map_aux D.atlas.hπ hπ Φ ψ₂ hΦ.continuous heq
    hcomm₂ u u₀ hv.symm (FundamentalGroup.fromPath ⟦η⟧)
  have hcol : b65s_column (hπ.fundamentalGroupToMulOpposite u) (FundamentalGroup.fromPath ⟦η⟧) =
      b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
        (FundamentalGroup.fromPath ⟦η.map (Homeomorph.setCongr hU).continuous⟧) := by
    simp only [b65s_column, MonoidHom.comp_apply]
    rw [key]
    rfl
  rw [hA, hcol]
  exact hT (η.map (Homeomorph.setCongr hU).continuous)

/-- **The inverse sphere maps form a continuous family** on the polydisc: the graph is the
solution set of a continuous equation and the target is compact. -/
theorem b65g_sphere_inv (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) :
    ∃ E : b6t_polydisc c × OnePoint ℂ → OnePoint ℂ, Continuous E ∧
      ∀ t w, b6t_sphere c t.val (E (t, w)) = w ∧ E (t, b6t_sphere c t.val w) = w := by
  choose H hH using fun t : b6t_polydisc c ↦ b6t_homeomorph c hc t.val t.property
  refine ⟨fun q ↦ (H q.1).symm q.2, ?_, fun t w ↦ ⟨?_, ?_⟩⟩
  · apply continuous_of_isClosed_graph
    have : Function.graph (fun q : b6t_polydisc c × OnePoint ℂ ↦ (H q.1).symm q.2) =
        {p | b6t_sphere c p.1.1.val p.2 = p.1.2} := by
      ext ⟨⟨t, w⟩, z⟩
      change (H t).symm w = z ↔ b6t_sphere c t.val z = w
      rw [Homeomorph.symm_apply_eq, ← hH, eq_comm]
    rw [this]
    exact isClosed_eq ((b6t_continuous c hc).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (continuous_snd.comp continuous_fst)
  · change b6t_sphere c t.val ((H t).symm w) = w
    rw [← hH, Homeomorph.apply_symm_apply]
  · change (H t).symm (b6t_sphere c t.val w) = w
    rw [← hH, Homeomorph.symm_apply_apply]

/-- **Free homotopies of loops preserve the deck monodromy**, with the fibre point carried along
the trace of the base point. -/
theorem b65g_monodromy_free_homotopy {U X G : Type*} [TopologicalSpace U] [TopologicalSpace X]
    [Group G] [MulAction G U] {π : U → X} (hπ : IsQuotientCoveringMap π G) (F : C(I × I, X))
    {y₀ y₁ : X} (γ₀ : Path y₀ y₀) (γ₁ : Path y₁ y₁)
    (h0 : ∀ s, F (0, s) = γ₀ s) (h1 : ∀ s, F (1, s) = γ₁ s) (hside : ∀ τ, F (τ, 0) = F (τ, 1))
    (w₀ : π ⁻¹' {y₀}) (w₁ : π ⁻¹' {y₁}) (Γ : C(I, U)) (hΓ0 : Γ 0 = w₀) (hΓ1 : Γ 1 = w₁)
    (hΓ : ∀ τ, π (Γ τ) = F (τ, 0)) :
    hπ.fundamentalGroupToMulOpposite w₁ (FundamentalGroup.fromPath ⟦γ₁⟧) =
      hπ.fundamentalGroupToMulOpposite w₀ (FundamentalGroup.fromPath ⟦γ₀⟧) := by
  have cov := hπ.isCoveringMap
  set g := (hπ.fundamentalGroupToMulOpposite w₀ (FundamentalGroup.fromPath ⟦γ₀⟧)).unop with hg
  have hγ0 : γ₀.toContinuousMap 0 = π (w₀ : U) := by
    change γ₀ 0 = _; rw [γ₀.source]; exact w₀.2.symm
  let Λ := cov.liftPath γ₀.toContinuousMap w₀ hγ0
  have hΛ1 : Λ 1 = g • (w₀ : U) := by
    have := hπ.unop_fundamentalGroupToMulOpposite_smul (e := w₀)
      (γ := FundamentalGroup.fromPath ⟦γ₀⟧)
    rw [← hg] at this
    rw [this]
    exact (cov.coe_monodromy_mk γ₀ w₀).symm
  have hH0 : ∀ s, F (0, s) = π (Λ s) := by
    intro s
    rw [h0]
    exact (congrFun (cov.liftPath_lifts γ₀.toContinuousMap w₀ hγ0) s).symm
  have hL := cov.liftHomotopy_lifts F Λ hH0
  have hL0 := cov.liftHomotopy_zero F Λ hH0
  set L := cov.liftHomotopy F Λ hH0 with hLdef
  -- the side `s = 0` of the lift is `Γ`
  have hside0 : (fun τ ↦ L (τ, 0)) = Γ := by
    apply cov.eq_of_comp_eq (L.continuous.comp (Continuous.prodMk_left 0)) Γ.continuous
      _ 0
    · change L (0, 0) = Γ 0
      rw [hL0, hΓ0]
      exact cov.liftPath_zero _ _ _
    · funext τ
      change π (L (τ, 0)) = π (Γ τ)
      rw [hΓ]
      exact congrFun hL (τ, 0)
  -- the side `s = 1` is `g • Γ`
  have hside1 : (fun τ ↦ L (τ, 1)) = fun τ ↦ g • Γ τ := by
    apply cov.eq_of_comp_eq (L.continuous.comp (Continuous.prodMk_left 1))
      ((hπ.continuous_const_smul g).comp Γ.continuous) _ 0
    · change L (0, 1) = g • Γ 0
      rw [hL0, hΓ0]
      exact hΛ1
    · funext τ
      change π (L (τ, 1)) = π (g • Γ τ)
      rw [hπ.map_smul, hΓ, hside]
      exact congrFun hL (τ, 1)
  let Γ₁ : C(I, U) := ⟨fun s ↦ L (1, s), L.continuous.comp (Continuous.prodMk_right 1)⟩
  have key := hπ.fundamentalGroupToMulOpposite_apply_mk_eq (e := w₁) (γ := γ₁) (g := g)
    (Γ := Γ₁) ?_ ?_ ?_
  · rw [← MulOpposite.op_unop (hπ.fundamentalGroupToMulOpposite w₀ _), ← hg]
    exact key
  · funext s
    change π (L (1, s)) = γ₁ s
    rw [← h1]
    exact congrFun hL (1, s)
  · change L (1, 0) = w₁
    rw [← hΓ1]
    exact congrFun hside0 1
  · change L (1, 1) = g • (w₁ : U)
    rw [← hΓ1]
    exact congrFun hside1 1

/-- An indexed Fuchsian coefficient is analytic off its poles. -/
theorem b65g_coefficient_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) :
    AnalyticOnNhd ℂ (b65p_coefficient E t A) (Set.range t)ᶜ := by
  intro z hz
  have : b65p_coefficient E t A = ∑ q, fun w ↦ (w - t q)⁻¹ • A q := by
    funext w; simp [b65p_coefficient]
  rw [this]
  apply Finset.analyticAt_sum
  intro q _
  have h1 : AnalyticAt ℂ (fun w : ℂ ↦ (w - t q)⁻¹) z :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr fun h ↦ hz ⟨q, h.symm⟩)
  exact h1.smul analyticAt_const

/-- The radial push off the discs of radius `δ` about the points `c q`. -/
def b65g_pushField {ι : Type*} [Fintype ι] (c : ι → ℂ) (δ : ℝ) (z : ℂ) : ℂ :=
  ∑ q, ((max 1 (δ / dist z (c q)) - 1 : ℝ) : ℂ) * (z - c q)

theorem b65g_pushField_single {ι : Type*} [Fintype ι] (c : ι → ℂ) (δ : ℝ)
    (hsep : ∀ q q', q ≠ q' → 2 * δ < dist (c q) (c q')) (z : ℂ) (q₀ : ι)
    (h : dist z (c q₀) < δ) :
    b65g_pushField c δ z = ((max 1 (δ / dist z (c q₀)) - 1 : ℝ) : ℂ) * (z - c q₀) := by
  classical
  unfold b65g_pushField
  rw [Finset.sum_eq_single q₀]
  · intro q _ hq
    have h2 := hsep q₀ q (Ne.symm hq)
    have h3 : δ ≤ dist z (c q) := by
      have := dist_triangle (c q₀) z (c q)
      rw [dist_comm (c q₀) z] at this
      linarith
    have h4 : δ / dist z (c q) ≤ 1 := by
      rcases (le_or_gt δ 0) with hδ | hδ
      · exact (div_nonpos_of_nonpos_of_nonneg hδ dist_nonneg).trans zero_le_one
      · exact (div_le_one (lt_of_lt_of_le hδ h3)).mpr h3
    rw [max_eq_left h4]
    simp
  · intro h; exact absurd (Finset.mem_univ q₀) h

theorem b65g_pushField_far {ι : Type*} [Fintype ι] (c : ι → ℂ) (δ : ℝ) (z : ℂ)
    (h : ∀ q, δ ≤ dist z (c q)) : b65g_pushField c δ z = 0 := by
  unfold b65g_pushField
  apply Finset.sum_eq_zero
  intro q _
  have h4 : δ / dist z (c q) ≤ 1 := by
    rcases (le_or_gt δ 0) with hδ | hδ
    · exact (div_nonpos_of_nonpos_of_nonneg hδ dist_nonneg).trans zero_le_one
    · exact (div_le_one (lt_of_lt_of_le hδ (h q))).mpr (h q)
  rw [max_eq_left h4]
  simp

/-- **Pushing loops off small discs.** For discs of radius `δ` about separated points `c q` and
a base point outside them, every loop in the complement of the points is homotopic there to a
loop staying at distance at least `δ` from every `c q`. -/
theorem b65g_push_off (c : Fin 4 ⊕ Fin 12 → ℂ) (δ : ℝ)
    (hsep : ∀ q q', q ≠ q' → 2 * δ < dist (c q) (c q')) {x : b65g_U c}
    (hx : ∀ q, δ < dist (x : ℂ) (c q)) (η : Path x x) :
    ∃ η' : Path x x, η.Homotopic η' ∧ ∀ s q, δ ≤ dist (η' s : ℂ) (c q) := by
  classical
  -- the push at time `τ`
  let H : ℝ → ℂ → ℂ := fun τ z ↦ z + (τ : ℂ) * b65g_pushField c δ z
  have hnear : ∀ z q₀, dist z (c q₀) < δ → z ≠ c q₀ → ∀ τ ∈ Icc (0 : ℝ) 1,
      H τ z - c q₀ = ((1 + τ * (δ / dist z (c q₀) - 1) : ℝ) : ℂ) * (z - c q₀) ∧
        dist z (c q₀) ≤ (1 + τ * (δ / dist z (c q₀) - 1)) * dist z (c q₀) ∧
        (1 + τ * (δ / dist z (c q₀) - 1)) * dist z (c q₀) ≤ δ := by
    intro z q₀ hz hne τ hτ
    have hd : 0 < dist z (c q₀) := dist_pos.mpr hne
    have hm : 1 ≤ δ / dist z (c q₀) := (one_le_div hd).mpr hz.le
    refine ⟨?_, ?_, ?_⟩
    · simp only [H, b65g_pushField_single c δ hsep z q₀ hz, max_eq_right hm]
      push_cast
      ring
    · nlinarith [mul_nonneg hτ.1 (sub_nonneg.mpr hm)]
    · have : (1 + τ * (δ / dist z (c q₀) - 1)) * dist z (c q₀) =
          dist z (c q₀) + τ * (δ - dist z (c q₀)) := by field_simp
      rw [this]
      nlinarith [hτ.2, hz]
  have hfar : ∀ z, (∀ q, δ ≤ dist z (c q)) → ∀ τ, H τ z = z := by
    intro z hz τ
    simp [H, b65g_pushField_far c δ z hz]
  -- the push stays in the complement, and at time one it is `δ` away from every point
  have hstay : ∀ z : ℂ, z ∉ Set.range c → ∀ τ ∈ Icc (0 : ℝ) 1,
      H τ z ∉ Set.range c ∧ (τ = 1 → ∀ q, δ ≤ dist (H τ z) (c q)) := by
    intro z hz τ hτ
    by_cases hc : ∃ q₀, dist z (c q₀) < δ
    · obtain ⟨q₀, hq₀⟩ := hc
      have hne : z ≠ c q₀ := fun h ↦ hz ⟨q₀, h.symm⟩
      obtain ⟨h1, h2, h3⟩ := hnear z q₀ hq₀ hne τ hτ
      have hd : 0 < dist z (c q₀) := dist_pos.mpr hne
      have hnorm : dist (H τ z) (c q₀) = (1 + τ * (δ / dist z (c q₀) - 1)) * dist z (c q₀) := by
        rw [dist_eq_norm, h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (by nlinarith [mul_nonneg hτ.1 (sub_nonneg.mpr ((one_le_div hd).mpr hq₀.le))]),
          ← dist_eq_norm]
      have hother : ∀ q, q ≠ q₀ → δ < dist (H τ z) (c q) := by
        intro q hq
        have := hsep q₀ q (Ne.symm hq)
        have t1 := dist_triangle (c q₀) (H τ z) (c q)
        rw [dist_comm (c q₀) (H τ z)] at t1
        linarith
      refine ⟨?_, fun hτ1 q ↦ ?_⟩
      · rintro ⟨q, hq⟩
        by_cases hqq : q = q₀
        · subst hqq
          have : dist (H τ z) (c q) = 0 := by rw [← hq, dist_self]
          linarith
        · have := hother q hqq
          rw [← hq, dist_self] at this
          linarith
      · by_cases hqq : q = q₀
        · subst hqq; subst hτ1
          rw [hnorm]
          have : (1 + 1 * (δ / dist z (c q) - 1)) * dist z (c q) = δ := by field_simp; ring
          rw [this]
        · exact (hother q hqq).le
    · simp only [not_exists, not_lt] at hc
      rw [hfar z hc τ]
      exact ⟨hz, fun _ ↦ hc⟩
  let K : Set ℂ := b65g_U c
  have hφ : ContinuousOn (b65g_pushField c δ) K := by
    have : b65g_pushField c δ =
        fun z ↦ ∑ q, ((max 1 (δ / dist z (c q)) - 1 : ℝ) : ℂ) * (z - c q) := rfl
    rw [this]
    apply continuousOn_finsetSum
    intro q _
    have hd : ContinuousOn (fun z : ℂ ↦ δ / dist z (c q)) K :=
      continuousOn_const.div (continuous_id.dist continuous_const).continuousOn
        (fun z hz ↦ dist_ne_zero.mpr (fun h ↦ hz ⟨q, h.symm⟩))
    exact (Complex.continuous_ofReal.comp_continuousOn
      ((ContinuousOn.sup continuousOn_const hd).sub continuousOn_const)).mul
      (continuous_id.sub continuous_const).continuousOn
  let Hc : C(I × K, K) :=
    ⟨fun p ↦ ⟨H p.1 p.2, (hstay p.2 p.2.prop p.1 p.1.prop).1⟩, by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_snd).add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
          (hφ.comp_continuous (continuous_subtype_val.comp continuous_snd)
            (fun p ↦ p.2.prop)))⟩
  have hHx : ∀ τ : I, Hc (τ, x) = x := fun τ ↦
    Subtype.ext (hfar _ (fun q ↦ (hx q).le) τ)
  let R : C(K, K) := ⟨fun z ↦ Hc (1, z), Hc.continuous.comp (Continuous.prodMk_right 1)⟩
  have hRx : R x = x := hHx 1
  let η' : Path x x := (η.map R.continuous).cast hRx.symm hRx.symm
  have hprop : ∀ (τ : I), ∀ s ∈ ({0, 1} : Set I), Hc (τ, η s) = η s := by
    intro τ s hs
    rcases hs with rfl | hs
    · rw [η.source]; exact hHx τ
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [η.target]; exact hHx τ
  let F : Path.Homotopy η η' :=
    { toFun := fun p ↦ Hc (p.1, η p.2)
      continuous_toFun := Hc.continuous.comp
        (continuous_fst.prodMk (η.continuous.comp continuous_snd))
      map_zero_left := fun s ↦ Subtype.ext (by simp [Hc, H])
      map_one_left := fun s ↦ rfl
      prop' := fun τ s hs ↦ hprop τ s hs }
  refine ⟨η', ⟨F⟩, ?_⟩
  · intro s q
    exact (hstay (η s) (η s).prop 1 ⟨zero_le_one, le_rfl⟩).2 rfl q

theorem b65g_poles_hasDerivAt (p : Fin 12 → ℂ) (q : Fin 4 ⊕ Fin 12) (θ : ℂ) :
    HasDerivAt (fun θ ↦ b65p_poles p θ q) (b65p_velocity p q) θ := by
  rcases q with k | j
  · simpa [b65p_poles, b65p_velocity] using hasDerivAt_const θ (b65p_fixedPole k)
  · simpa [b65p_poles, b65p_velocity] using
      ((hasDerivAt_id θ).mul_const (b65p_V (b65p_fibre j) (p j))).const_add (p j)

theorem b65g_poles_continuous (p : Fin 12 → ℂ) (q : Fin 4 ⊕ Fin 12) :
    Continuous (fun θ ↦ b65p_poles p θ q) :=
  continuous_iff_continuousAt.mpr fun θ ↦ (b65g_poles_hasDerivAt p q θ).continuousAt

theorem b65g_poles_analytic (p : Fin 12 → ℂ) (q : Fin 4 ⊕ Fin 12) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun θ ↦ b65p_poles p θ q) s := by
  intro θ _
  rcases q with k | j
  · exact analyticAt_const
  · exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)

/-- The normalized chart point is continuous on the disc of the record. -/
theorem b65g_curve_continuousOn (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ContinuousOn (b65p_curve p) (ball 0 O.radius) := by
  apply continuousOn_pi.mpr
  intro i θ hθ
  have hinj := O.poles_injective θ hθ
  have hc : ∀ j, Continuous (fun θ ↦ b65p_moving p θ j) := fun j ↦
    b65g_poles_continuous p (Sum.inr j)
  have hz : b65p_moving p θ (Fin.castLE (by norm_num) i) ≠ 0 := fun h ↦
    Sum.inr_ne_inl (hinj (a₁ := Sum.inr (Fin.castLE (by norm_num) i)) (a₂ := Sum.inl 0) h)
  have hab : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := by
    intro h
    have := hinj (a₁ := Sum.inr 11) (a₂ := Sum.inr 10) (sub_eq_zero.mp h)
    simp at this
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun θ ↦ (b65p_moving p θ (Fin.castLE (by norm_num) i) -
    b65p_moving p θ 10) * b65p_moving p θ 11 / (b65p_moving p θ (Fin.castLE (by norm_num) i) *
      (b65p_moving p θ 11 - b65p_moving p θ 10))) θ
  exact ((((hc _).sub (hc 10)).mul (hc 11)).continuousAt).div
    (((hc _).mul ((hc 11).sub (hc 10))).continuousAt) (mul_ne_zero hz hab)

theorem b65g_theta_transfer_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (t₀ : b6t_polydisc (b65z_centre p)) (ht₀ : t₀.val = b65p_curve p 0)
    (h₀ : ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t₀ (b65p_moving p 0 10)
        (b65p_moving p 0 11) (b65p_poles p 0)) b4b_Group,
      b65g_loopTransfer D t₀ (b65p_moving p 0 10) (b65p_moving p 0 11) (b65p_poles p 0)
        (O.residue 0) hπ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          (b65p_poles p θ)) b4b_Group,
        b65g_loopTransfer D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
          (O.residue θ) hπ := by
  classical
  obtain rfl : t₀ = b65z_s₀ (b65z_centre p) := Subtype.ext ht₀
  obtain ⟨hπ₀, x₀, u₀, C₀, hT₀⟩ := h₀
  have hR := O.radius_pos
  have h0R : (0 : ℂ) ∈ ball (0 : ℂ) O.radius := mem_ball_self hR
  have hinj0 := O.poles_injective 0 h0R
  -- the separation radius `δ`
  obtain ⟨δ, hδ, hsep0, hx0⟩ : ∃ δ : ℝ, 0 < δ ∧
      (∀ q q', q ≠ q' → 8 * δ < dist (b65p_poles p 0 q) (b65p_poles p 0 q')) ∧
      ∀ q, 8 * δ < dist (x₀ : ℂ) (b65p_poles p 0 q) := by
    have hlim : Tendsto (fun d : ℝ ↦ 8 * d) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_const_mul (8 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have e1 : ∀ᶠ d in 𝓝[>] (0 : ℝ), ∀ q q', q ≠ q' →
        8 * d < dist (b65p_poles p 0 q) (b65p_poles p 0 q') := by
      rw [Filter.eventually_all]; intro q
      rw [Filter.eventually_all]; intro q'
      by_cases hq : q = q'
      · exact Eventually.of_forall fun _ h ↦ absurd hq h
      · have hpos : 0 < dist (b65p_poles p 0 q) (b65p_poles p 0 q') :=
          dist_pos.mpr fun h ↦ hq (hinj0 h)
        exact (hlim.eventually (gt_mem_nhds hpos)).mono fun _ h _ ↦ h
    have e2 : ∀ᶠ d in 𝓝[>] (0 : ℝ), ∀ q, 8 * d < dist (x₀ : ℂ) (b65p_poles p 0 q) := by
      rw [Filter.eventually_all]; intro q
      have hpos : 0 < dist (x₀ : ℂ) (b65p_poles p 0 q) :=
        dist_pos.mpr fun h ↦ x₀.property ⟨q, h.symm⟩
      exact hlim.eventually (gt_mem_nhds hpos)
    obtain ⟨d, ⟨h1, h2⟩, h3⟩ := (e1.and e2).and self_mem_nhdsWithin |>.exists
    exact ⟨d, h3, h1, h2⟩
  -- the radius `ε`
  obtain ⟨ε, hε, hεR, hmove⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε, ∀ q,
      dist (b65p_poles p θ q) (b65p_poles p 0 q) < δ / 2 := by
    have e : ∀ᶠ θ in 𝓝 (0 : ℂ), ∀ q, dist (b65p_poles p θ q) (b65p_poles p 0 q) < δ / 2 := by
      rw [Filter.eventually_all]; intro q
      exact ((b65g_poles_continuous p q).tendsto 0).eventually (ball_mem_nhds _ (by linarith))
    obtain ⟨ε₀, hε₀, h⟩ := Metric.eventually_nhds_iff.mp e
    exact ⟨min ε₀ O.radius, lt_min hε₀ hR, min_le_right _ _,
      fun θ hθ ↦ h (lt_of_lt_of_le hθ (min_le_left _ _))⟩
  refine ⟨ε, hε, hεR, fun θ hθ t ht ↦ ?_⟩
  have hθR : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball hεR hθ
  have hπ := b65g_quotientCovering_aux p O g D θ hθR t ht
  refine ⟨hπ, ?_⟩
  have hdist : ∀ θ' ∈ ball (0 : ℂ) ε, ∀ q,
      dist (b65p_poles p θ' q) (b65p_poles p θ q) < δ := by
    intro θ' hθ' q
    have h1 := hmove θ' hθ' q
    have h2 := hmove θ hθ q
    have := dist_triangle_right (b65p_poles p θ' q) (b65p_poles p θ q) (b65p_poles p 0 q)
    linarith
  have hsep : ∀ q q', q ≠ q' → 2 * δ < dist (b65p_poles p θ q) (b65p_poles p θ q') := by
    intro q q' hq
    have h1 := hsep0 q q' hq
    have h2 := hmove θ hθ q
    have h3 := hmove θ hθ q'
    have := dist_triangle4 (b65p_poles p 0 q) (b65p_poles p θ q) (b65p_poles p θ q')
      (b65p_poles p 0 q')
    rw [dist_comm (b65p_poles p 0 q) (b65p_poles p θ q)] at this
    linarith
  have hxfar : ∀ q, δ < dist (x₀ : ℂ) (b65p_poles p θ q) := by
    intro q
    have h1 := hx0 q
    have h2 := hmove θ hθ q
    have := dist_triangle (x₀ : ℂ) (b65p_poles p θ q) (b65p_poles p 0 q)
    linarith
  let x' : b65g_U (b65p_poles p θ) := ⟨x₀.val, fun ⟨q, hq⟩ ↦ by
    have := hxfar q
    rw [← hq, dist_self] at this
    linarith⟩
  -- the regular locus at `0` in the atlas cover
  obtain ⟨ha0, hb0, hab0⟩ := b65g_moving_ne p O 0 h0R
  obtain ⟨M0, hM0, hMk0⟩ := O.normalization 0 h0R
  have hP0 : ∀ u, ((D.atlas.π u : OnePoint ℂ)) =
      b6t_sphere (b65z_centre p) (b65z_s₀ (b65z_centre p)).val (D.atlas.f (D.atlas.ι u)) := by
    intro u
    rw [show (b65z_s₀ (b65z_centre p)).val = (b65z_centre p) from rfl, b6t_identity, D.atlas.hproj]
    rfl
  obtain ⟨Φ₀, ψ₀, hΦ₀, hψ₀, heq₀, hcomm₀, -, hψv₀, -⟩ := b65g_regular_embedding D
    (b65z_s₀ (b65z_centre p)) _ _ _ ha0 hb0 hab0 ⟨Sum.inl 0, rfl⟩ M0 hM0
    (b65g_branch_of_pole p 0 _ rfl M0 hMk0) D.atlas.π hP0
  -- the regular locus at `θ` in the atlas cover
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθR
  obtain ⟨M, hM, hMk⟩ := O.normalization θ hθR
  obtain ⟨e, he⟩ := b6t_punctured_homeomorph (b65z_centre p) D.atlas.hb t.val t.property
  obtain ⟨Φ, ψ, hΦ, hψ, heq, hcomm, hrange, hψv, -⟩ := b65g_regular_embedding D t _ _ _ ha hb
    hab ⟨Sum.inl 0, rfl⟩ M hM (b65g_branch_of_pole p θ t.val ht M hMk) (e ∘ D.atlas.π)
    (fun u ↦ by rw [Function.comp_apply, he, ← D.atlas.hproj])
  obtain ⟨E, hEc, hE⟩ := b65g_sphere_inv (b65z_centre p) D.atlas.hb
  -- the segment of parameters from `0` to `θ`
  have hτ : ∀ τ : I, ((τ : ℝ) : ℂ) * θ ∈ ball (0 : ℂ) ε := by
    intro τ
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg τ.2.1]
    have := mem_ball_zero_iff.mp hθ
    nlinarith [τ.2.2, norm_nonneg θ]
  have hτR : ∀ τ : I, ((τ : ℝ) : ℂ) * θ ∈ ball (0 : ℂ) O.radius := fun τ ↦
    ball_subset_ball hεR (hτ τ)
  let tt : I → b6t_polydisc (b65z_centre p) := fun τ ↦
    ⟨b65p_curve p (((τ : ℝ) : ℂ) * θ), (O.curve_mem _ (hτR τ)).1⟩
  have hscal : Continuous (fun τ : I ↦ ((τ : ℝ) : ℂ) * θ) :=
    (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const
  have htt : Continuous tt :=
    ((b65g_curve_continuousOn p O).comp_continuous hscal hτR).subtype_mk _
  let av : I → ℂ := fun τ ↦ b65p_moving p (((τ : ℝ) : ℂ) * θ) 10
  let bv : I → ℂ := fun τ ↦ b65p_moving p (((τ : ℝ) : ℂ) * θ) 11
  have hav : Continuous av := (b65g_poles_continuous p (Sum.inr 10)).comp hscal
  have hbv : Continuous bv := (b65g_poles_continuous p (Sum.inr 11)).comp hscal
  have habv : ∀ τ, bv τ - av τ ≠ 0 := fun τ h ↦
    (b65g_moving_ne p O _ (hτR τ)).2.2 (sub_eq_zero.mp h).symm
  let Fun : I → ℂ → OnePoint ℂ := fun τ z ↦
    E (tt τ, ((b65s_normalize (av τ) (bv τ) z : ℂ) : OnePoint ℂ))
  have hFun_mem : ∀ (τ : I) (z : ℂ), (∀ q, z ≠ b65p_poles p (((τ : ℝ) : ℂ) * θ) q) →
      Fun τ z ∈ b6t_punctured (b65z_centre p) := by
    intro τ z hz ⟨k, hk⟩
    obtain ⟨ha', hb', hab'⟩ := b65g_moving_ne p O _ (hτR τ)
    obtain ⟨M', hM', hMk'⟩ := O.normalization _ (hτR τ)
    obtain ⟨q, hq⟩ := b65g_branch_of_pole p (((τ : ℝ) : ℂ) * θ) _ rfl M' hMk' k
    have hz0 : z ≠ 0 := hz (Sum.inl 0)
    have h1 := congrArg (b6t_sphere (b65z_centre p) (tt τ).val) hk
    rw [b6t_marks (b65z_centre p) D.atlas.hb _ (tt τ).property, (hE _ _).1] at h1
    have h2 : M' (z : OnePoint ℂ) = M' (b65p_poles p (((τ : ℝ) : ℂ) * θ) q : OnePoint ℂ) := by
      rw [hq, hM', (b65g_sCoord_mobius _ _ z ha' hb' hab' hz0).1]
      exact h1.symm
    exact hz q (OnePoint.coe_injective (M'.injective h2))
  have hFun_cont : ∀ ξ : I → ℂ, Continuous ξ → (∀ s, ξ s ≠ 0) →
      Continuous (fun q : I × I ↦ Fun q.1 (ξ q.2)) := by
    intro ξ hξc hξ
    refine hEc.comp ((htt.comp continuous_fst).prodMk (OnePoint.continuous_coe.comp ?_))
    change Continuous (fun q : I × I ↦ (ξ q.2 - av q.1) * bv q.1 / (ξ q.2 * (bv q.1 - av q.1)))
    exact (((hξc.comp continuous_snd).sub (hav.comp continuous_fst)).mul
      (hbv.comp continuous_fst)).div ((hξc.comp continuous_snd).mul
        ((hbv.comp continuous_fst).sub (hav.comp continuous_fst)))
      (fun q ↦ mul_ne_zero (hξ q.2) (habv q.1))
  have htt0 : tt 0 = b65z_s₀ (b65z_centre p) := by
    apply Subtype.ext
    show b65p_curve p (((((0 : I) : ℝ)) : ℂ) * θ) = b65p_curve p 0
    simp
  have htt1 : tt 1 = t := by
    apply Subtype.ext
    show b65p_curve p (((((1 : I) : ℝ)) : ℂ) * θ) = t.val
    rw [ht]; simp
  have hav0 : av 0 = b65p_moving p 0 10 := by simp [av]
  have hbv0 : bv 0 = b65p_moving p 0 11 := by simp [bv]
  have hav1 : av 1 = b65p_moving p θ 10 := by simp [av]
  have hbv1 : bv 1 = b65p_moving p θ 11 := by simp [bv]
  have hE0 : ∀ w, E (b65z_s₀ (b65z_centre p), w) = w := fun w ↦ by
    have := (hE (b65z_s₀ (b65z_centre p)) w).2
    rwa [show (b65z_s₀ (b65z_centre p)).val = b65z_centre p from rfl, b6t_identity] at this
  have hFun0 : ∀ z, z ≠ 0 →
      Fun 0 z = b65p_mobius (b65p_moving p 0 10) (b65p_moving p 0 11) z := by
    intro z hz
    show E (tt 0, ((b65s_normalize (av 0) (bv 0) z : ℂ) : OnePoint ℂ)) = _
    rw [htt0, hE0, hav0, hbv0, (b65g_sCoord_mobius _ _ z ha0 hb0 hab0 hz).1]
  have hFun1 : ∀ z, z ≠ 0 → b6t_sphere (b65z_centre p) t.val (Fun 1 z) =
      b65p_mobius (b65p_moving p θ 10) (b65p_moving p θ 11) z := by
    intro z hz
    show b6t_sphere (b65z_centre p) t.val
      (E (tt 1, ((b65s_normalize (av 1) (bv 1) z : ℂ) : OnePoint ℂ))) = _
    rw [htt1, (hE _ _).1, hav1, hbv1, (b65g_sCoord_mobius _ _ z ha hb hab hz).1]
  clear_value Fun
  have hx0τ : ∀ (τ : I) q, (x₀ : ℂ) ≠ b65p_poles p (((τ : ℝ) : ℂ) * θ) q := by
    intro τ q h
    have h1 := hx0 q
    have h2 := hmove _ (hτ τ) q
    rw [← h] at h2
    linarith
  have hx0ne : (x₀ : ℂ) ≠ 0 := hx0τ 0 (Sum.inl 0)
  -- the trace of the base point and its lift through the atlas cover
  have hβc : Continuous (fun τ : I ↦ Fun τ x₀) :=
    (hFun_cont (fun _ ↦ (x₀ : ℂ)) continuous_const (fun _ ↦ hx0ne)).comp
      (Continuous.prodMk_left (0 : I))
  let β : C(I, b6t_punctured (b65z_centre p)) :=
    ⟨fun τ ↦ ⟨Fun τ x₀, hFun_mem τ x₀ (hx0τ τ)⟩, hβc.subtype_mk _⟩
  have hβ0 : β 0 = D.atlas.π (Φ₀ u₀.val) := by
    apply Subtype.ext
    rw [hcomm₀, u₀.property, hψv₀]
    exact hFun0 _ hx0ne
  have cov := D.atlas.hπ.isCoveringMap
  let Γ := cov.liftPath β (Φ₀ u₀.val) hβ0
  have hΓπ : ∀ τ, D.atlas.π (Γ τ) = β τ := fun τ ↦
    congrFun (cov.liftPath_lifts β (Φ₀ u₀.val) hβ0) τ
  have hw₁ : e (D.atlas.π (Γ 1)) = ψ x' := by
    apply Subtype.ext
    rw [he, hΓπ, hψv]
    exact hFun1 _ hx0ne
  obtain ⟨v, hv⟩ : Γ 1 ∈ Set.range Φ := by
    rw [hrange]
    exact ⟨x', hw₁.symm⟩
  have hvx : b65g_sProj D t _ _ _ v = x' := by
    apply hψ.injective
    rw [← hcomm v, Function.comp_apply, hv]
    exact hw₁
  let u'' : b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) ⁻¹' {x'} :=
    ⟨v, hvx⟩
  -- the isomonodromy operator at `θ`
  obtain ⟨-, -, hiso⟩ := b65p_schlesinger_isomonodromic (Fin 4 → ℂ) ε
    (fun θ q ↦ b65p_poles p θ q) O.residue (fun q ↦ b65g_poles_analytic p q _)
    (fun θ' hθ' ↦ O.poles_injective θ' (ball_subset_ball hεR hθ'))
    (fun θ' hθ' q ↦ by
      have hvel : (fun q ↦ deriv (fun θ ↦ b65p_poles p θ q) θ') = b65p_velocity p :=
        funext fun q ↦ (b65g_poles_hasDerivAt p q θ').deriv
      rw [hvel]
      exact O.schlesinger θ' (ball_subset_ball hεR hθ') q)
  obtain ⟨G, hG⟩ := hiso (x₀ : ℂ) θ hθ
  refine ⟨x', u'', G * C₀, fun η ↦ ?_⟩
  obtain ⟨η', hηη', hfar⟩ := b65g_push_off (b65p_poles p θ) δ hsep hxfar η
  have havoid : ∀ θ' ∈ ball (0 : ℂ) ε, ∀ s q, (η' s : ℂ) ≠ b65p_poles p θ' q := by
    intro θ' hθ' s q h
    have h1 := hfar s q
    have h2 := hdist θ' hθ' q
    rw [← h] at h2
    linarith
  have hη'0 : ∀ s, (η' s : ℂ) ≠ 0 := fun s ↦ havoid θ hθ s (Sum.inl 0)
  have hUopen : IsOpen (b65g_U (b65p_poles p θ)) :=
    (Set.finite_range _).isClosed.isOpen_compl
  have hT1 := b65f_homotopy_invariance (Fin 4 → ℂ) (b65g_U (b65p_poles p θ)) hUopen
    (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ))
    (b65g_coefficient_analytic _ _) x' x' η η' hηη'
  let η₀ : Path x₀ x₀ :=
    { toFun := fun s ↦ ⟨(η' s : ℂ), fun ⟨q, hq⟩ ↦ havoid 0 (mem_ball_self hε) s q hq.symm⟩
      continuous_toFun := (continuous_subtype_val.comp η'.continuous).subtype_mk _
      source' := by apply Subtype.ext; show (η' 0 : ℂ) = (x₀ : ℂ); rw [η'.source]
      target' := by apply Subtype.ext; show (η' 1 : ℂ) = (x₀ : ℂ); rw [η'.target] }
  have hT2 : b65f_transport (Fin 4 → ℂ)
      (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ))
      (fun v ↦ (η'.extend v : ℂ)) =
      G.val * (C₀.val * (b65s_column (hπ₀.fundamentalGroupToMulOpposite u₀)
        (FundamentalGroup.fromPath ⟦η₀⟧)).val * (C₀⁻¹).val) * (G⁻¹).val := by
    rw [← hT₀ η₀]
    exact hG (η'.map continuous_subtype_val) (fun θ' hθ' s q ↦ havoid θ' hθ' s q)
  -- the free homotopy in the punctured sphere at the centre
  let F : C(I × I, b6t_punctured (b65z_centre p)) :=
    ⟨fun q ↦ ⟨Fun q.1 (η' q.2), hFun_mem q.1 _ (fun q' ↦ havoid _ (hτ q.1) q.2 q')⟩,
      (hFun_cont (fun s ↦ (η' s : ℂ)) (continuous_subtype_val.comp η'.continuous)
        hη'0).subtype_mk _⟩
  let ψθC : C(b65g_U (b65p_poles p θ), b6t_punctured (b65z_centre p)) :=
    ⟨fun z ↦ e.symm (ψ z), e.symm.continuous.comp hψ.continuous⟩
  have hcommθ : ∀ w, D.atlas.π (Φ w) = ψθC (b65g_sProj D t _ _ _ w) := fun w ↦ by
    show _ = e.symm (ψ _)
    rw [← hcomm w, Function.comp_apply, Homeomorph.symm_apply_apply]
  let eθ : D.atlas.π ⁻¹' {ψθC x'} := ⟨Γ 1, by
    show D.atlas.π (Γ 1) = e.symm (ψ x')
    rw [← hw₁, Homeomorph.symm_apply_apply]⟩
  let ψ₀C : C(b65g_U (b65p_poles p 0), b6t_punctured (b65z_centre p)) := ⟨ψ₀, hψ₀.continuous⟩
  let e₀ : D.atlas.π ⁻¹' {ψ₀C x₀} := ⟨Φ₀ u₀.val, by
    show D.atlas.π (Φ₀ u₀.val) = ψ₀ x₀
    rw [hcomm₀, u₀.property]⟩
  have hfree := b65g_monodromy_free_homotopy D.atlas.hπ F (η₀.map ψ₀C.continuous)
    (η'.map ψθC.continuous) ?_ ?_ ?_ e₀ eθ Γ (cov.liftPath_zero β _ hβ0) rfl ?_
  rotate_left
  · intro s
    apply Subtype.ext
    show Fun 0 (η' s) = ((ψ₀ (η₀ s)) : OnePoint ℂ)
    rw [hψv₀, hFun0 _ (hη'0 s)]
    rfl
  · intro s
    show F (1, s) = e.symm (ψ (η' s))
    apply (Homeomorph.eq_symm_apply e).mpr
    apply Subtype.ext
    rw [he, hψv]
    exact hFun1 _ (hη'0 s)
  · intro τ
    apply Subtype.ext
    show Fun τ (η' 0) = Fun τ (η' 1)
    rw [η'.source, η'.target]
  · intro τ
    rw [hΓπ]
    apply Subtype.ext
    show Fun τ x₀ = Fun τ (η' 0)
    rw [η'.source]
  have hcol : b65s_column (hπ.fundamentalGroupToMulOpposite u'')
      (FundamentalGroup.fromPath ⟦η⟧) =
      b65s_column (hπ₀.fundamentalGroupToMulOpposite u₀) (FundamentalGroup.fromPath ⟦η₀⟧) := by
    have h1 : FundamentalGroup.fromPath ⟦η⟧ = FundamentalGroup.fromPath ⟦η'⟧ := by
      congr 1
      exact Quotient.sound hηη'
    simp only [b65s_column, MonoidHom.comp_apply]
    rw [h1, caf_fundamentalGroupToMulOpposite_map_aux D.atlas.hπ hπ Φ ψθC hΦ.continuous heq
      hcommθ u'' eθ hv.symm, caf_fundamentalGroupToMulOpposite_map_aux D.atlas.hπ hπ₀ Φ₀ ψ₀C
      hΦ₀.continuous heq₀ hcomm₀ u₀ e₀ rfl]
    exact congrArg _ (congrArg _ hfree)
  rw [hT1, hT2, hcol, Units.val_mul, _root_.mul_inv_rev, Units.val_mul]
  simp only [mul_assoc]

theorem b65g_all_loop_transfer_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          (b65p_poles p θ)) b4b_Group,
        b65g_loopTransfer D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
          (O.residue θ) hπ :=
  b65g_theta_transfer_aux p O g D (b65z_s₀ (b65z_centre p)) rfl
    (b65g_base_transfer_aux p O g D e he x u₀ C hT (b65z_s₀ (b65z_centre p)) rfl)

end HodgeLean.Foundations.Program
