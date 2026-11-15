import HodgeLean.Foundations.Program.PrymParabolicSkeletaModels

/-! # Proofs for stage H3b step C, first part: skeleta and the degree-one comparison

The `_aux` theorems that `PrymParabolicSkeleta.lean` restates, with bodies. The generic statements
(finite closed skeleta, `H₀` of the vertices, the two connecting maps) are direct computations
with explicit classes (`PrymParabolicSkeletaLemmas.lean`); the cell statements for the lifted
triangles come from the base cells and unique lifting; the skeletal relative groups come from the
attached-cell theorem of `PrymParabolicSkeletaCells.lean` with the model cells of
`PrymParabolicSkeletaModels.lean`; the comparison on `H₁` is the chase through the two long exact
sequences (`hg8_H1map_bijective_of`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Convexity

namespace HodgeLean.Foundations.Program

theorem hg8_skel_closed_aux {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    [T2Space T] (F : hg8_DeltaMap g T) :
    (hg8_skel0 F).Finite ∧ IsClosed (hg8_skel0 F) ∧ IsClosed (hg8_skel1 F) := by
  have h0 : (hg8_skel0 F).Finite := Set.finite_range _
  refine ⟨h0, h0.isClosed, ?_⟩
  refine h0.isClosed.union (isClosed_iUnion_of_finite fun ε ↦ ?_)
  exact (isCompact_range (F.edge ε).continuous).isClosed

theorem hg8_skel_cells_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL))ᶜ = ⋃ τ, L τ '' {a : StdSimplex ℝ (Fin 3) | ∀ k, 0 < a.weights k} ∧
      hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) \ hg8_skel0 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) =
        ⋃ ε, hg5_liftEdge L ε '' Set.Ioo 0 1 := by
  obtain ⟨hbd, hint, hev⟩ := hg8_lift_skel U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨hcov, -⟩ := hg5_lift_cells U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι hιG L hL
  obtain ⟨hends, -⟩ := hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  refine ⟨Set.ext fun c ↦ ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩, Set.ext fun c ↦ ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩⟩
  · obtain ⟨τ, a, rfl⟩ := hcov c
    by_cases ha : ∀ k, 0 < a.weights k
    · exact Set.mem_iUnion.2 ⟨τ, a, ha, rfl⟩
    · exact absurd (hbd τ a ha) hc
  · obtain ⟨τ, a, ha, rfl⟩ := Set.mem_iUnion.1 hc
    exact hint τ a ha
  · obtain ⟨h1, h0⟩ := hc
    rcases h1 with h1 | h1
    · exact absurd h1 h0
    obtain ⟨ε, s, rfl⟩ := Set.mem_iUnion.1 h1
    refine Set.mem_iUnion.2 ⟨ε, s, ?_, rfl⟩
    by_contra hs
    rcases hg8_unit_endpoint s hs with rfl | rfl
    · exact h0 ⟨_, (hends ε).1.symm⟩
    · exact h0 ⟨_, (hends ε).2.symm⟩
  · obtain ⟨ε, s, hs, rfl⟩ := Set.mem_iUnion.1 hc
    exact ⟨Or.inr (Set.mem_iUnion.2 ⟨ε, s, rfl⟩), fun ⟨v, hv⟩ ↦ hev ε s hs v hv.symm⟩

theorem hg8_edge_embed_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ ε, Topology.IsClosedEmbedding (hg5_liftEdge L ε)) ∧
      (∀ (ε ε' : hg2_Edge G 13) (s s' : unitInterval), s ∈ Set.Ioo 0 1 → s' ∈ Set.Ioo 0 1 →
        hg5_liftEdge L ε s = hg5_liftEdge L ε' s' → ε = ε' ∧ s = s') ∧
      (∀ (ε : hg2_Edge G 13) (s : unitInterval), s ∈ Set.Ioo 0 1 →
        ∀ v, hg5_liftEdge L ε s ≠ hg5_liftVert g L v) := by
  obtain ⟨-, -, hc, hd, -⟩ := hg5_open_cells
  have hfe := hg8_f_liftEdge f L (fun τ ↦ (hL τ).1)
  obtain ⟨hends, hvinj⟩ := hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr
    hstab ι hι hιr hfι hιG L hL
  refine ⟨fun ε ↦ ?_, fun ε ε' s s' hs hs' h ↦ ?_, fun ε s hs v h ↦ ?_⟩
  · refine (hg5_liftEdge L ε).continuous.isClosedEmbedding fun s s' h ↦ ?_
    have h' := congrArg f h
    rw [hfe, hfe] at h'
    exact hg8_edge_injective _ h'
  · have h' := congrArg f h
    rw [hfe, hfe] at h'
    obtain ⟨hb, rfl⟩ := hc _ _ _ _ hs hs' h'
    refine ⟨?_, rfl⟩
    have key : ∀ (S : Set unitInterval), _root_.IsPreconnected S → s ∈ S → ∀ t₀ ∈ S,
        (∀ t ∈ S, hg5_edge (hg8_edgeBase ε) t ∉ Set.range (b6_branch mr_base)) →
        hg5_liftEdge L ε t₀ = hg5_liftEdge L ε' t₀ := by
      intro S hS hsS t₀ ht₀ hm
      refine hg8_lift_unique_on π hπ f ι hι hιr hfι _ _ S hS (fun t _ ↦ ?_) (fun t ht ↦ ?_) hsS ht₀ h
      · rw [hfe, hfe, hb]
      · rw [hfe]; exact hm t ht
    have hIco : ∀ (i : Fin 13) (t : unitInterval), t ∈ Set.Ico 0 1 →
        hg5_edge (Sum.inl (i, ())) t ∉ Set.range (b6_branch mr_base) := by
      intro i t ht hm
      rcases (hg5_edge_marks _ t).1 hm with ⟨i', -, rfl⟩ | ⟨i', h2, -⟩
      · exact lt_irrefl _ ht.2
      · cases h2
    have hF : ∀ (i : Fin 13) (t : unitInterval),
        hg5_edge (Sum.inr (Sum.inl (i, ()))) t ∉ Set.range (b6_branch mr_base) := by
      intro i t hm
      rcases (hg5_edge_marks _ t).1 hm with ⟨i', h2, -⟩ | ⟨i', h2, -⟩ <;> cases h2
    have hIoc : ∀ (i : Fin 13) (t : unitInterval), t ∈ Set.Ioc 0 1 →
        hg5_edge (Sum.inr (Sum.inr (i, ()))) t ∉ Set.range (b6_branch mr_base) := by
      intro i t ht hm
      rcases (hg5_edge_marks _ t).1 hm with ⟨i', h2, -⟩ | ⟨i', -, rfl⟩
      · cases h2
      · exact lt_irrefl _ ht.1
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;> rcases ε' with ⟨j, y⟩ | ⟨j, y⟩ | ⟨j, y⟩ <;>
      simp only [hg8_edgeBase, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq,
        and_true] at hb
    · subst hb
      have h0 := key (Set.Ico 0 1) isPreconnected_Ico ⟨le_of_lt hs.1, hs.2⟩ 0
        ⟨le_rfl, zero_lt_one⟩ (hIco i)
      rw [(hends _).1, (hends _).1] at h0
      have := hvinj h0
      simp only [hg2_src, Sum.inl.injEq] at this
      rw [this]
    · subst hb
      have h0 := key Set.univ isPreconnected_univ (Set.mem_univ _) 0 (Set.mem_univ _)
        (fun t _ ↦ hF i t)
      rw [(hends _).1, (hends _).1] at h0
      have := hvinj h0
      simp only [hg2_src, Sum.inl.injEq] at this
      rw [this]
    · subst hb
      have h1 := key (Set.Ioc 0 1) isPreconnected_Ioc ⟨hs.1, le_of_lt hs.2⟩ 1
        ⟨zero_lt_one, le_rfl⟩ (hIoc i)
      rw [(hends _).2, (hends _).2] at h1
      have := hvinj h1
      simp only [hg2_tgt, Sum.inr.injEq, Sum.inl.injEq, mul_left_inj] at this
      rw [this]
  · obtain ⟨ε', hε'⟩ := hg8_vert_end g v
    have hv : ∃ e : unitInterval, e ∉ Set.Ioo 0 1 ∧ hg5_liftVert g L v = hg5_liftEdge L ε' e := by
      rcases hε' with rfl | rfl
      · exact ⟨0, fun h ↦ lt_irrefl _ h.1, (hends ε').1.symm⟩
      · exact ⟨1, fun h ↦ lt_irrefl _ h.2, (hends ε').2.symm⟩
    obtain ⟨e, he, hve⟩ := hv
    obtain ⟨w, hw⟩ := hg8_edge_endpoint_vert (hg8_edgeBase ε') e he
    have h' := congrArg f h
    rw [hve, hfe, hfe, hw] at h'
    exact hd _ s hs w h'

theorem hg8_tri_attach_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    ∀ τ, Topology.IsClosedEmbedding (L τ) ∧ IsOpen (L τ '' {a : StdSimplex ℝ (Fin 3) | ∀ k, 0 < a.weights k}) ∧
      L τ '' {a : StdSimplex ℝ (Fin 3) | ∀ k, 0 < a.weights k}ᶜ ⊆ hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) := by
  obtain ⟨hbd, hint, -⟩ := hg8_lift_skel U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨hcov, huniq⟩ := hg5_lift_cells U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι hιG L hL
  intro τ
  refine ⟨(L τ).continuous.isClosedEmbedding fun a a' h ↦ ?_, ?_, ?_⟩
  · have h' := congrArg f h
    rw [(hL τ).1, (hL τ).1] at h'
    exact hg5_tri_injective _ h'
  · have heq : L τ '' {a : StdSimplex ℝ (Fin 3) | ∀ k, 0 < a.weights k} =
        (hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL))ᶜ ∩
          ⋂ τ', ⋂ (_ : τ' ≠ τ), (Set.range (L τ'))ᶜ := by
      ext c
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨hint τ a ha, Set.mem_iInter₂.2 fun τ' hτ' ⟨a', ha'⟩ ↦ ?_⟩
        by_cases h' : ∀ k, 0 < a'.weights k
        · exact hτ' (huniq τ' τ a' a h' ha ha').1
        · exact hint τ a ha (ha' ▸ hbd τ' a' h')
      · rintro ⟨hc, hc'⟩
        obtain ⟨τ'', a, rfl⟩ := hcov c
        by_cases ha : ∀ k, 0 < a.weights k
        · by_cases hτ : τ'' = τ
          · exact ⟨a, ha, by rw [hτ]⟩
          · exact absurd ⟨a, rfl⟩ (Set.mem_iInter₂.1 hc' τ'' hτ)
        · exact absurd (hbd τ'' a ha) hc
    rw [heq]
    refine ((hg8_skel_closed_aux _).2.2.isOpen_compl).inter
      (isOpen_iInter_of_finite fun τ' ↦ isOpen_iInter_of_finite fun _ ↦ ?_)
    exact (isCompact_range (L τ').continuous).isClosed.isOpen_compl
  · rintro _ ⟨a, ha, rfl⟩
    exact hbd τ a ha

theorem hg8_vertClass_bijective_aux {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    [T2Space T] (F : hg8_DeltaMap g T)
    (hinj : Function.Injective F.vert) :
    Function.Bijective (hg8_vertClass F) := by
  classical
  let X := (Subtype.val ⁻¹' hg8_skel0 F : Set (hg8_skel1 F))
  have hfin : Finite X := by
    have : Finite (hg8_skel0 F) := (Set.finite_range F.vert).to_subtype
    exact Finite.of_injective (fun x : X ↦ (⟨x.1.1, x.2⟩ : hg8_skel0 F))
      (fun a b h ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
  have hdisc : DiscreteTopology X := inferInstance
  let K := SingularChainComplex ℤ (hg8_pair10 F).snd
  have hd : ∀ i (a : K.X i), (K.d i 0).hom a = 0 := by
    intro i a
    by_cases hi : i = 1
    · subst hi
      change Simplicial.boundary ℤ 0 (X := TopCat.toSSet.obj (TopCat.of X)) a = 0
      rw [hg8_boundary_discrete X]
      rfl
    · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
      rfl
  have hv0 : Function.Injective (hg8_vert0 F) := fun a b h ↦
    hinj (congrArg (fun x : X ↦ (x.1.1 : T)) h)
  constructor
  · intro c₁ c₂ hc
    rw [← sub_eq_zero, ← map_sub] at hc
    rw [← sub_eq_zero]
    set c := c₁ - c₂
    have h1 : hg5_chain0 (hg8_vert0 F) c = 0 := by
      obtain ⟨a, ha⟩ := (hg8_homologyClass_eq_zero_iff (K.sc 0) _).1 hc
      exact ha.symm.trans (hd _ a)
    ext v
    rw [Finsupp.zero_apply]
    let f : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)) → ℤ :=
      fun σ ↦ if TopCat.toSSetObj₀Equiv σ = hg8_vert0 F v then 1 else 0
    have h2 := congrArg (hg8_simplexFun ℤ _ 0 f) h1
    rw [map_zero] at h2
    rw [← h2]
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, Finsupp.add_apply, ha, hb]
    | single u n =>
      simp only [hg5_chain0, Finsupp.linearCombination_single]
      erw [LinearMap.map_smul, hg8_simplexFun_chainOfSimplex]
      simp only [f, hg5_pointSimplex, Equiv.apply_symm_apply, hv0.eq_iff, Finsupp.single_apply,
        smul_eq_mul]
      split_ifs <;> simp_all
  · have hsurj : ∀ x : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)), ∃ v, hg8_vert0 F v =
        TopCat.toSSetObj₀Equiv x := by
      intro x
      obtain ⟨v, hv⟩ := (TopCat.toSSetObj₀Equiv x).2
      exact ⟨v, Subtype.ext (Subtype.ext hv)⟩
    have htop : LinearMap.range (hg5_chain0 (hg8_vert0 F)) = ⊤ := by
      apply hg8_range_eq_top
      intro σ
      obtain ⟨v, hv⟩ := hsurj σ
      refine ⟨Finsupp.single v 1, ?_⟩
      rw [hg5_chain0, Finsupp.linearCombination_single, hg5_pointSimplex, hv,
        Equiv.symm_apply_apply]
      erw [one_smul]
    intro y
    obtain ⟨w, rfl⟩ := ShortComplex.moduleCatHomologyClass_surjective _ y
    obtain ⟨c, hc⟩ := LinearMap.range_eq_top.1 htop w.1
    refine ⟨c, ?_⟩
    change ShortComplex.moduleCatHomologyClass _ (LinearMap.codRestrict _ _ _ c) = _
    congr 1
    exact Subtype.ext hc

theorem hg8_edgeRel_bijective_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    Function.Bijective (hg8_edgeRel (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) ∧
      ∀ n, n ≠ 1 → Subsingleton (RelativeHomology ℤ (hg8_pair10 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) n) := by
  classical
  let F := hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨hemb, hdisj, hnv⟩ := hg8_edge_embed_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨hends, -⟩ := hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  have hcells : hg8_Cells (Subtype.val ⁻¹' hg8_skel0 F : Set (hg8_skel1 F)) hg8_Iends
      (hg8_edge1 F) := by
    have hint : ∀ s : unitInterval, s ∉ hg8_Iends → s ∈ Set.Ioo 0 1 := fun s hs ↦ by
      rcases hg8_unit_endpoint' s with h | h | h
      · exact absurd (Or.inl h) hs
      · exact absurd (Or.inr h) hs
      · exact h
    refine ⟨(hg8_skel_closed_aux F).2.1.preimage continuous_subtype_val, fun ε ↦ ?_,
      fun ε s hs ↦ ?_, fun ε s hs ⟨v, hv⟩ ↦ hnv ε s (hint s hs) v hv.symm,
      fun ε ε' s s' hs hs' h ↦ (hdisj ε ε' s s' (hint s hs) (hint s' hs')
        (congrArg Subtype.val h)).1, fun x hx ↦ ?_⟩
    · exact (hg8_edge1 F ε).continuous.isClosedEmbedding fun s s' h ↦
        (hemb ε).injective (congrArg Subtype.val h)
    · rcases hs with rfl | rfl
      · exact ⟨_, (hends ε).1.symm⟩
      · exact ⟨_, (hends ε).2.symm⟩
    · rcases x.2 with h | h
      · exact absurd h hx
      · obtain ⟨ε, s, hs⟩ := Set.mem_iUnion.1 h
        exact ⟨ε, s, Subtype.ext hs⟩
  have hchain : ∀ ε, hg8_chainMap (hg8_edge1 F ε) 1
      (hg5_chain1 (fun _ : Unit ↦ ContinuousMap.id unitInterval) (Finsupp.single () 1)) =
      hg5_chain1 (hg8_edge1 F) (Finsupp.single ε 1) := by
    intro ε
    rw [hg8_chain1_map]
    simp only [hg5_chain1, Finsupp.linearCombination_single]
    rfl
  have hcell : ∀ ε, relativeHomologyMap ℤ 1 (hg8_cellMap hcells ε) hg8_Igen =
      hg8_edgeRel F (Finsupp.single ε 1) := by
    intro ε
    refine (hg8_relClass_map ℤ (hg8_cellMap hcells ε) 0 ⟨_, hg8_Iid_relCycle⟩
      (by
        have h := hg8_edge_relCycle F (Finsupp.single ε 1)
        rw [← hchain ε] at h
        exact h)).trans ?_
    exact congrArg (hg8_relClass ℤ (hg8_pair10 F) 0) (Subtype.ext (hchain ε))
  have : Fintype (hg2_Edge G 13) := Fintype.ofFinite _
  have hsum : ∀ c : hg2_Edge G 13 →₀ ℤ, hg8_edgeRel F c =
      ∑ ε, relativeHomologyMap ℤ 1 (hg8_cellMap hcells ε) (c ε • hg8_Igen) := by
    intro c
    conv_lhs => rw [← Finsupp.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ε _ ↦ ?_
    rw [map_zsmul, hcell]
    refine (congrArg (hg8_edgeRel F) ?_).trans (map_zsmul (hg8_edgeRel F) (c ε) _)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨⟨fun c c' h ↦ ?_, fun x ↦ ?_⟩, fun k hk ↦ ⟨fun x y ↦ ?_⟩⟩
  · rw [← sub_eq_zero] at h ⊢
    rw [← map_sub, hsum] at h
    ext ε
    exact hg8_Igen_smul_eq_zero _ (hg8_cells_independent ℤ hcells hg8_Imodel 1 _ h ε)
  · obtain ⟨y, hy⟩ := hg8_cells_span ℤ hcells hg8_Imodel 1 x
    choose n hn using fun ε ↦ hg8_I_H1_span (y ε)
    refine ⟨Finsupp.equivFunOnFinite.symm n, ?_⟩
    rw [hsum, hy]
    refine Finset.sum_congr rfl fun ε _ ↦ ?_
    rw [hn ε]
    rfl
  · obtain ⟨y', hy'⟩ := hg8_cells_span ℤ hcells hg8_Imodel k x
    obtain ⟨y'', hy''⟩ := hg8_cells_span ℤ hcells hg8_Imodel k y
    rw [hy', hy'']
    refine Finset.sum_congr rfl fun ε _ ↦ ?_
    rw [hg8_I_H_eq_zero k hk (y' ε), hg8_I_H_eq_zero k hk (y'' ε)]

theorem hg8_triRel_bijective_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    Function.Bijective (hg8_triRel (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) ∧
      ∀ n, n ≠ 2 → Subsingleton (RelativeHomology ℤ (hg8_pair21 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) n) := by
  classical
  let F := hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨hbd, hint, -⟩ := hg8_lift_skel U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨-, huniq⟩ := hg5_lift_cells U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι hιG L hL
  have hatt := hg8_tri_attach_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  obtain ⟨hcells1, -⟩ := hg8_skel_cells_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  have hpos : ∀ a : StdSimplex ℝ (Fin 3), a ∉ hg8_bd → ∀ k, 0 < a.weights k := fun a ha k ↦
    lt_of_le_of_ne (a.weights_nonneg k) fun h ↦ ha ⟨k, h.symm⟩
  have hcells : hg8_Cells (hg8_skel1 F) hg8_bd L := by
    refine ⟨(hg8_skel_closed_aux F).2.2, fun τ ↦ (hatt τ).1, fun τ a ha ↦ hbd τ a ?_,
      fun τ a ha ↦ hint τ a (hpos a ha), fun τ τ' a a' ha ha' h ↦
        (huniq τ τ' a a' (hpos a ha) (hpos a' ha') h).1, fun x hx ↦ ?_⟩
    · obtain ⟨k, hk⟩ := ha
      exact fun h ↦ (h k).ne' hk
    · have : x ∈ (hg8_skel1 F)ᶜ := hx
      rw [hcells1] at this
      obtain ⟨τ, a, -, rfl⟩ := Set.mem_iUnion.1 this
      exact ⟨τ, a, rfl⟩
  have hchain : ∀ τ, hg8_chainMap (L τ) 2
      (hg5_chain2 (fun _ : Unit ↦ ContinuousMap.id (StdSimplex ℝ (Fin 3))) (Finsupp.single () 1)) =
      hg5_chain2 L (Finsupp.single τ 1) := by
    intro τ
    rw [hg8_chain2_map]
    simp only [hg5_chain2, Finsupp.linearCombination_single]
    rfl
  have hcell : ∀ τ, relativeHomologyMap ℤ 2 (hg8_cellMap hcells τ) hg8_Tgen =
      hg8_triRel F (Finsupp.single τ 1) := by
    intro τ
    refine (hg8_relClass_map ℤ (hg8_cellMap hcells τ) 1 ⟨_, hg8_Tid_relCycle⟩
      (by
        have h : (hg5_chain2 L (Finsupp.single τ 1) :
            (SingularChainComplex ℤ (hg8_pair21 F).fst).X (1 + 1)) ∈
            hg8_relCycles ℤ (hg8_pair21 F) 1 := hg8_tri_relCycle F (Finsupp.single τ 1)
        rw [← hchain τ] at h
        exact h)).trans ?_
    exact congrArg (hg8_relClass ℤ (hg8_pair21 F) 1) (Subtype.ext (hchain τ))
  have : Fintype (hg2_Tri G 13) := Fintype.ofFinite _
  have hsum : ∀ c : hg2_Tri G 13 →₀ ℤ, hg8_triRel F c =
      ∑ τ, relativeHomologyMap ℤ 2 (hg8_cellMap hcells τ) (c τ • hg8_Tgen) := by
    intro c
    conv_lhs => rw [← Finsupp.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [map_zsmul, hcell]
    refine (congrArg (hg8_triRel F) ?_).trans (map_zsmul (hg8_triRel F) (c τ) _)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨⟨fun c c' h ↦ ?_, fun x ↦ ?_⟩, fun k hk ↦ ⟨fun x y ↦ ?_⟩⟩
  · rw [← sub_eq_zero] at h ⊢
    rw [← map_sub, hsum] at h
    ext τ
    exact hg8_Tgen_smul_eq_zero _ (hg8_cells_independent ℤ hcells hg8_Tmodel 2 _ h τ)
  · obtain ⟨y, hy⟩ := hg8_cells_span ℤ hcells hg8_Tmodel 2 x
    choose n hn using fun τ ↦ hg8_T_H2_span (y τ)
    refine ⟨Finsupp.equivFunOnFinite.symm n, ?_⟩
    rw [hsum, hy]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [hn τ]
    rfl
  · obtain ⟨y', hy'⟩ := hg8_cells_span ℤ hcells hg8_Tmodel k x
    obtain ⟨y'', hy''⟩ := hg8_cells_span ℤ hcells hg8_Tmodel k y
    rw [hy', hy'']
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [hg8_T_H_eq_zero k hk (y' τ), hg8_T_H_eq_zero k hk (y'' τ)]

theorem hg8_connecting1_aux {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (c : hg2_Edge G r →₀ ℤ) :
    hg8_delta (hg8_pair10 F) 0 (hg8_edgeRel F c) = hg8_vertClass F (hg2_bd1 ℤ g c) := by
  have hends : ∀ ε, hg8_edge1 F ε 0 = hg8_vert1 F (hg2_src g ε) ∧
      hg8_edge1 F ε 1 = hg8_vert1 F (hg2_tgt g ε) :=
    fun ε ↦ ⟨Subtype.ext (F.ends ε).1, Subtype.ext (F.ends ε).2⟩
  refine hg8_delta_class _ (relativeChainShortComplex_shortExact ℤ (hg8_pair10 F)) 0 _
    (hg5_chain1 (hg8_edge1 F) c) rfl _ ?_
  change hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 0
      (hg5_chain0 (hg8_vert0 F) (hg2_bd1 ℤ g c)) =
    Simplicial.boundary ℤ 0 (hg5_chain1 (hg8_edge1 F) c)
  rw [hg8_chain0_map, hg5_bd_chain1 (hg8_edge1 F) (hg8_vert1 F) _ _ hends c]
  rfl

theorem hg8_connecting2_aux {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (w : hg2_Tri G r →₀ ℤ) :
    hg8_proj (hg8_pair10 F) 1 (hg8_delta (hg8_pair21 F) 1 (hg8_triRel F w)) =
      hg8_edgeRel F (hg2_bd2 ℤ g w) := by
  have hS := relativeChainShortComplex_shortExact ℤ (hg8_pair21 F)
  have hx₁ : ((relativeChainShortComplex ℤ (hg8_pair21 F)).f.f 1).hom
      (hg5_chain1 (hg8_edge1 F) (hg2_bd2 ℤ g w)) =
      ((relativeChainShortComplex ℤ (hg8_pair21 F)).X₂.d (1 + 1) 1).hom (hg5_chain2 F.tri w) := by
    change hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 1
        (hg5_chain1 (hg8_edge1 F) (hg2_bd2 ℤ g w)) =
      Simplicial.boundary ℤ 1 (hg5_chain2 F.tri w)
    rw [hg8_chain1_map, hg5_bd_chain2 F.tri F.edge _ _ _ F.faces w]
    rfl
  have hk : (hg5_chain1 (hg8_edge1 F) (hg2_bd2 ℤ g w) :
      (SingularChainComplex ℤ (hg8_pair10 F).fst).X 1) ∈
      LinearMap.ker ((SingularChainComplex ℤ (hg8_pair10 F).fst).sc 1).g.hom :=
    hS.d_eq_zero_of_f_eq_d_apply _ _ _ _ hx₁ _
  have e : hg8_delta (hg8_pair21 F) 1 (hg8_triRel F w) =
      ((SingularChainComplex ℤ (hg8_pair10 F).fst).sc 1).moduleCatHomologyClass ⟨_, hk⟩ :=
    hg8_delta_class _ hS 1 _ (hg5_chain2 F.tri w) rfl ⟨_, hk⟩ hx₁
  rw [e]
  unfold hg8_proj relativeHomologyProjection
  exact ShortComplex.moduleCatHomologyClass_naturality _ _

/-- **The degree-one comparison from the skeletal groups.** For a `Δ`-map with injective vertices
whose edge classes are a basis of `H₁(T¹, T⁰)`, whose triangle classes span `H₂(T, T¹)` and with
`H₁(T, T¹) = 0`, the induced map on `H₁` is bijective.
Source: Hatcher, *Algebraic Topology*, Lemma 2.34 and Theorem 2.35. -/
theorem hg8_H1map_bijective_of {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] [T2Space T] (F : hg8_DeltaMap g T)
    (hinj : Function.Injective F.vert) (h6 : Function.Bijective (hg8_edgeRel F))
    (h7 : Function.Surjective (hg8_triRel F))
    (h7' : ∀ x : RelativeHomology ℤ (hg8_pair21 F) 1, x = 0) :
    Function.Bijective (hg8_H1map F) := by
  let X := (Subtype.val ⁻¹' hg8_skel0 F : Set (hg8_skel1 F))
  have hfin : Finite X := by
    have : Finite (hg8_skel0 F) := (Set.finite_range F.vert).to_subtype
    exact Finite.of_injective (fun x : X ↦ (⟨x.1.1, x.2⟩ : hg8_skel0 F))
      (fun a b h ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
  have h0 : ∀ a : Homology ℤ (hg8_pair10 F).snd 1, a = 0 :=
    hg8_homology_discrete_eq_zero X one_ne_zero
  have hP := relativeChainShortComplex_shortExact ℤ (hg8_pair10 F)
  have hQ := relativeChainShortComplex_shortExact ℤ (hg8_pair21 F)
  have eP := (ShortComplex.moduleCat_exact_iff _).1 (hP.homology_exact₂ 1)
  have eQ := (ShortComplex.moduleCat_exact_iff _).1 (hQ.homology_exact₂ 1)
  have eQ₁ := (ShortComplex.moduleCat_exact_iff _).1 (hQ.homology_exact₁ 2 1 (by simp))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← hg8_skelClass_incl] at hx
    obtain ⟨t, ht⟩ := eQ₁ _ hx
    obtain ⟨w, rfl⟩ := h7 t
    have h9 := hg8_connecting2_aux F w
    have ht' : hg8_delta (hg8_pair21 F) 1 (hg8_triRel F w) = hg8_skelClass F z := ht
    rw [ht'] at h9
    change (HomologicalComplex.homologyMap (relativeChainShortComplex ℤ (hg8_pair10 F)).g 1).hom
      (hg8_skelClass F z) = _ at h9
    rw [hg8_skelClass_proj] at h9
    have hzw := h6.1 h9
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨w, hzw.symm⟩
  · intro y
    obtain ⟨x, hx⟩ := eQ y (h7' _)
    change Homology ℤ (TopCat.of (hg8_skel1 F)) 1 at x
    obtain ⟨c, hc⟩ := h6.2
      ((HomologicalComplex.homologyMap (relativeChainShortComplex ℤ (hg8_pair10 F)).g 1).hom x)
    have hδ : hg8_delta (hg8_pair10 F) 0 (hg8_edgeRel F c) = 0 := by
      rw [hc]
      exact ConcreteCategory.congr_hom (hP.comp_δ 1 0 (by simp)) x
    rw [hg8_connecting1_aux] at hδ
    have hc0 : hg2_bd1 ℤ g c = 0 :=
      (hg8_vertClass_bijective_aux F hinj).1 (hδ.trans (map_zero _).symm)
    let z : LinearMap.ker (hg2_bd1 ℤ g) := ⟨c, hc0⟩
    have hxz : (HomologicalComplex.homologyMap (relativeChainShortComplex ℤ (hg8_pair10 F)).g 1).hom
        (x - hg8_skelClass F z) = 0 := by
      refine (LinearMap.map_sub _ _ _).trans ?_
      rw [hg8_skelClass_proj, ← hc]
      exact sub_self _
    obtain ⟨a, ha⟩ := eP _ hxz
    obtain rfl : a = 0 := h0 a
    have hx' : x = hg8_skelClass F z := sub_eq_zero.1 (ha.symm.trans (map_zero _))
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [← hg8_skelClass_incl, ← hx', ← hx]

theorem hg8_H1map_bijective_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    Function.Bijective (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) := by
  obtain ⟨h6, -⟩ := hg8_edgeRel_bijective_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr
    hstab ι hι hιr hfι hιG L hL
  obtain ⟨h7, h7z⟩ := hg8_triRel_bijective_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr
    hstab ι hι hιr hfι hιG L hL
  exact hg8_H1map_bijective_of _
    (hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι
      hιG L hL).2 h6 h7.2 fun x ↦ (h7z 1 (by norm_num)).elim x 0

theorem hg8_H1map_deck_aux {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer G c) = orderOf (g j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (h : G) (x : hg2_H1 ℤ g) :
    hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) (hg2_H1act ℤ g h x) =
      homologyMap ℤ 1 (TopCat.ofHom ⟨fun c : C ↦ h • c, hC h⟩) (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) x) := by
  let F := hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  let φ : C(C, C) := ⟨fun c : C ↦ h • c, hC h⟩
  have htri : ∀ τ, φ.comp (L τ) = L (hg2_actTri h τ) := fun τ ↦ ContinuousMap.ext fun a ↦
    hg5_lift_deck U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι L hL h τ a
  have hedge : ∀ ε, φ.comp (F.edge ε) = F.edge (hg2_actEdge h ε) := by
    rintro (⟨i, y⟩ | ⟨i, y⟩ | ⟨i, y⟩)
    · change φ.comp (hg5_face _ _) = hg5_face (L (hg2_actTri h (Sum.inl (i, y)))) 2
      rw [← htri]
      rfl
    · change φ.comp (hg5_face _ _) = hg5_face (L (hg2_actTri h (Sum.inl (i, y)))) 1
      rw [← htri]
      rfl
    · change φ.comp (hg5_face _ _) = hg5_face (L (hg2_actTri h (Sum.inl (i, y)))) 0
      rw [← htri]
      rfl
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc : hg8_chainMap φ 1 (hg5_chain1 F.edge z.1) =
      hg5_chain1 F.edge (hg2_chainAct1 ℤ h z.1) := by
    rw [hg8_chain1_map]
    simp only [hedge, hg2_chainAct1, Finsupp.lmapDomain_apply, hg5_chain1,
      Finsupp.linearCombination_mapDomain]
    rfl
  have e1 : ∀ z', hg8_H1map F (Submodule.Quotient.mk z') =
      ((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (hg8_cycle1 F z') :=
    fun _ ↦ rfl
  have e2 : hg2_H1act ℤ g h (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨hg2_chainAct1 ℤ h z.1, by
        rw [LinearMap.mem_ker, hg2_bd1_act, LinearMap.mem_ker.mp z.2, map_zero]⟩ := rfl
  rw [e2, e1, e1]
  let Fm := ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom φ)
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (.down ℕ) 1).map Fm
  change _ = (ShortComplex.homologyMap S).hom _
  refine (congrArg _ ?_).trans (ShortComplex.moduleCatHomologyClass_naturality S _).symm
  exact Subtype.ext hc.symm

end HodgeLean.Foundations.Program
