import HodgeLean.Foundations.Program.NamedLoopFamilyLoops

/-! # Specified named-loop family: the tuple and the retained family

Group-theoretic inputs for the Nielsen class of the tuple read off a cover with specified
monodromy, and the assembly of a retained family on a given cover.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- Loops presenting a group with the product relation generate it: the inclusion of the
generated subgroup is an epimorphism of groups.
Source: Mathlib `GrpCat.epi_iff_surjective`. -/
theorem b65w_closure_of_unique {M : Type} [Group M] {r : ℕ} (γ : Fin r → M)
    (hprod : (List.ofFn γ).prod = 1)
    (huniv : ∀ (H : Type) [Group H] (k : Fin r → H), (List.ofFn k).prod = 1 →
      ∃! φ : M →* H, ∀ j, φ (γ j) = k j) :
    Subgroup.closure (Set.range γ) = ⊤ := by
  set N := Subgroup.closure (Set.range γ)
  have hepi : CategoryTheory.Epi (GrpCat.ofHom N.subtype) := by
    constructor
    intro Z u v huv
    have hk : (List.ofFn (fun j ↦ u.hom (γ j))).prod = 1 := by
      have h := map_list_prod u.hom (List.ofFn γ)
      rw [hprod, map_one, List.map_ofFn] at h
      exact h.symm
    obtain ⟨φ, -, huniq⟩ := huniv Z (fun j ↦ u.hom (γ j)) hk
    have h1 := huniq u.hom (fun j ↦ rfl)
    have h2 := huniq v.hom (fun j ↦ by
      have := congrArg (fun w ↦ w.hom (⟨γ j, Subgroup.subset_closure ⟨j, rfl⟩⟩ : N)) huv
      simpa using this.symm)
    exact GrpCat.Hom.ext (h1.trans h2.symm)
  have hs := (GrpCat.epi_iff_surjective _).mp hepi
  rw [eq_top_iff]
  intro m _
  obtain ⟨n, hn⟩ := hs m
  have hn' : (n : M) = m := hn
  exact hn' ▸ n.property

/-- Equal class multisets are related by a permutation of the entries up to conjugacy. -/
theorem b65w_perm_of_classes {G : Type*} [Group G] {r : ℕ} (g g' : Fin r → G)
    (h : b4_classes g = b4_classes g') :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, IsConj (g i) (g' (σ i)) := by
  classical
  let F : Fin r → ConjClasses G := fun i ↦ ConjClasses.mk (g i)
  let F' : Fin r → ConjClasses G := fun i ↦ ConjClasses.mk (g' i)
  have hm : Multiset.map F Finset.univ.val = Multiset.map F' Finset.univ.val := by
    rw [Fin.univ_val_map, Fin.univ_val_map]
    simp only [b4_classes, List.map_ofFn] at h
    exact h
  have hcard : ∀ a, Fintype.card {i // F i = a} = Fintype.card {i // F' i = a} := by
    intro a
    have := congrArg (Multiset.count a) hm
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card, Finset.card,
      Finset.filter_val, Finset.filter_val]
    simpa only [eq_comm] using this
  let e : ∀ a, {i // F i = a} ≃ {i // F' i = a} := fun a ↦ Fintype.equivOfCardEq (hcard a)
  let σ : Equiv.Perm (Fin r) :=
    ((Equiv.sigmaFiberEquiv F).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv F')
  refine ⟨σ, fun i ↦ ?_⟩
  have hF : F' (σ i) = F i := (e (F i) ⟨i, rfl⟩).property
  exact ConjClasses.mk_eq_mk_iff_isConj.mp hF.symm

/-- Conjugacy in the group transfers conjugacy to a class representative. -/
theorem b65w_conjIn_of_isConj (c : Matrix (Fin 4) (Fin 4) ℂ) (a b : b4b_Group)
    (hab : IsConj a b) (hb : g32h_ConjIn c (b4b_toMatrix b)) :
    g32h_ConjIn c (b4b_toMatrix a) := by
  obtain ⟨k, hk⟩ := isConj_iff.mp hab
  obtain ⟨h, hh, h', hh', hhh', hbe⟩ := hb
  have ha : a = k⁻¹ * b * k := by rw [← hk]; group
  refine ⟨b4b_toMatrix k⁻¹ * h, g32h_G.mul_mem (k⁻¹).property hh,
    h' * b4b_toMatrix k, g32h_G.mul_mem hh' k.property, ?_, ?_⟩
  · calc b4b_toMatrix k⁻¹ * h * (h' * b4b_toMatrix k)
        = b4b_toMatrix k⁻¹ * (h * h') * b4b_toMatrix k := by simp only [mul_assoc]
      _ = 1 := by rw [hhh', mul_one, ← map_mul, inv_mul_cancel, map_one]
  · rw [ha, map_mul, map_mul, hbe]
    simp only [mul_assoc]

theorem b65w_isConj_inv {G : Type*} [Group G] {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨k, hk⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨k, by rw [← hk]; group⟩

/-- **The Nielsen class from the initial classes.** A generating product-one tuple whose entries
are, up to a permutation, conjugate to the inverses of the initial cut values lies in the G32
Nielsen class: the initial tuple shares its classes with the column root tuple.
Source: `b65b_path_replay`, `b65s_word_orbit`, `b65b_component`, `b4_classes_of_sameComponent`,
`b63d_root_nielsen`. -/
theorem b65w_nielsen (g : Fin 13 → b4b_Group) (hprod : (List.ofFn g).prod = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (τ : Equiv.Perm (Fin 13))
    (hconj : ∀ j, IsConj (g j) (b65b_initial (τ j))⁻¹) :
    g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := by
  have hc1 : b4_classes b65b_final = b4_classes b65b_initial := by
    rw [← b65b_path_replay]
    exact b4_classes_of_sameComponent (b65s_word_orbit _ _).1
  have hc2 : b4_classes b65b_final = b4_classes b65s_columnRoot :=
    b4_classes_of_sameComponent b65b_component
  obtain ⟨π, hπ⟩ := b65w_perm_of_classes b65b_initial b65s_columnRoot (hc1.symm.trans hc2)
  obtain ⟨σr, hσr⟩ := b63d_root_nielsen.1
  refine ⟨⟨τ.trans (π.trans (Fin.revPerm.trans σr)), fun j ↦ ?_⟩, ?_, ?_⟩
  · have h1 : IsConj (g j) (b4b_root (π (τ j)).rev) := by
      have h2 := b65w_isConj_inv (hπ (τ j))
      have h3 : (b65s_columnRoot (π (τ j)))⁻¹ = b4b_root (π (τ j)).rev := by
        simp [b65s_columnRoot]
      rw [h3] at h2
      exact (hconj j).trans h2
    exact b65w_conjIn_of_isConj _ _ _ h1 (hσr _)
  · have h := map_list_prod b4b_toMatrix (List.ofFn g)
    rw [hprod, map_one, List.map_ofFn] at h
    exact h.symm
  · apply le_antisymm
    · rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      exact (g i).property
    · intro m hm
      have key : ∀ a ∈ Subgroup.closure (Set.range g),
          b4b_toMatrix a ∈ Submonoid.closure (Set.range (fun i ↦ b4b_toMatrix (g i))) := by
        intro a ha
        induction ha using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Submonoid.subset_closure ⟨i, rfl⟩
        | one => rw [map_one]; exact Submonoid.one_mem _
        | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy
        | inv x _ hx =>
          have hpos : 0 < Fintype.card b4b_Group := Fintype.card_pos
          have hinv : x⁻¹ = x ^ (Fintype.card b4b_Group - 1) := by
            apply inv_eq_of_mul_eq_one_right
            rw [← pow_succ', Nat.sub_add_cancel hpos, pow_card_eq_one]
          rw [hinv, map_pow]
          exact Submonoid.pow_mem _ hx _
      have := key ⟨m, hm⟩ (by rw [hgen]; trivial)
      exact this

section Filling
open HurwitzPrymRexPunct HurwitzPrymRexFill Metric
attribute [local instance] b4b_group


/-- **The retained family on a given cover.** The construction of `b65z_family_construction`
with the cover of `b65z_marked_cover` replaced by a given connected cover whose fillings have
the rotation generators `g j`; the atlas keeps the given cover and its marked point.
Source: `b65z_family_construction`; `b65z_rot_transfer`, `b6a_fibre_geometry`,
`b6m_period_comparison`, `b63d_prymOperator_sq`. -/
theorem b65w_family_of_cover (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (g : Fin 13 → b4b_Group)
    (hne : ∀ j, g j ≠ 1)
    (U : Type) [TopologicalSpace U] [MulAction b4b_Group U] [ConnectedSpace U]
    (π : U → b6t_punctured c) (hπ : IsQuotientCoveringMap π b4b_Group)
    (hpos : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
        [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
        [FaithfulSMul b4b_Group C],
        (∀ k : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x)) →
        ∀ f : C → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover b4b_Group f →
        (∀ x, f x ∉ Set.range (b6_branch c) → MulAction.stabilizer b4b_Group x = ⊥) →
        ∀ ι : U → C, Continuous ι → (∀ u, f (ι u) = π u) →
        (∀ (k : b4b_Group) (u : U), ι (k • u) = k • ι u) →
        ∀ j, ∃ x, f x = b6_branch c j ∧ b4_IsRotGen ℂ x (g j))
    (y₀ : b6t_punctured c) (u₀ : π ⁻¹' {y₀}) :
    ∃ D : b65z_SharedFamily c g, ∃ u : D.atlas.π ⁻¹' {y₀},
      D.atlas.hπ.fundamentalGroupToMulOpposite u = hπ.fundamentalGroupToMulOpposite u₀ := by
  classical
  obtain ⟨S, hκ⟩ := b65z_standard_setup c U π u₀.1
  let κ := ContinuousLinearEquiv.refl ℂ ℂ
  let C := S.CC hπ κ
  let : TopologicalSpace C := b65z_fillTop c U π S hπ
  let : ChartedSpace ℂ C := b65z_fillChart c U π S hπ
  let : MulAction b4b_Group C := b65z_fillAction c U π S hπ
  let : IsManifold 𝓘(ℂ, ℂ) ω C := S.isManifold hπ κ
  let : T2Space C := S.instT2SpaceCC hπ κ
  let : LocallyCompactSpace (OnePoint ℂ) := ChartedSpace.locallyCompactSpace ℂ _
  let : CompactSpace C := S.instCompactSpaceCCOfLocallyCompactSpace hπ κ
  let : ConnectedSpace C := S.instConnectedSpaceCC hπ κ
  let f := S.f hπ κ
  let ι := S.ι hπ κ
  let n := b65z_fillOrder c U π S hπ
  have hn : ∀ x, 0 < n x := by
    rintro (u | d)
    · exact Nat.zero_lt_one
    · exact (S.D hπ d.1).e_pos
  have hunram : ∀ x, f x ∉ Set.range (b6_branch c) → n x = 1 := by
    rintro (u | d) hx
    · rfl
    · exact False.elim (hx d.1.property)
  have hlocal := b65z_fill_local c U π S hκ hπ
  have hf := S.contMDiff_f hπ κ
  have hgal : b4_IsGaloisCover b4b_Group f :=
    ⟨S.f_smul hπ κ, fun _ _ h ↦ S.exists_smul_of_f_eq hπ κ h⟩
  have hs : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ Set.range (b6_branch c)
    · exact ⟨S.ofP hπ κ ⟨⟨y, hy⟩, QuotientGroup.mk (1 : b4b_Group)⟩, rfl⟩
    · obtain ⟨u, hu⟩ := hπ.surjective ⟨y, hy⟩
      exact ⟨ι u, congrArg Subtype.val hu⟩
  have hG := S.contMDiff_smul hπ κ
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hG g).continuous
  have hι := S.isOpenEmbedding_ι hπ κ
  have hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch c))ᶜ := by
    ext x
    rcases x with u | d
    · exact ⟨fun _ ↦ (π u).property, fun _ ↦ ⟨u, rfl⟩⟩
    · exact ⟨fun ⟨u, hu⟩ ↦ False.elim (Sum.inl_ne_inr hu),
        fun h ↦ False.elim (h d.1.property)⟩
  have hproj : ∀ u, f (ι u) = π u := fun _ ↦ rfl
  have hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u := fun _ _ ↦ rfl
  have stab₀ := rf8_filling_stabilizers c U C π hπ u₀.1 f ι hι.injective hrange hequiv
  let : FaithfulSMul b4b_Group C := stab₀.1
  have hrot₀ := hpos C hG f hf hgal stab₀.2 ι hι.continuous hproj hequiv
  let A := b6a_isolatedFamilyChart c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  have hA := b6a_mem_isolatedFamilyChart_source c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous
  let cs := b6a_familyChartedSpace c C A hA
  let : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc c × C) := cs
  have hm := b6a_isolatedFamilyChart_isManifold c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  let : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc c × C) := hm
  have hform := b6a_isolatedFamilyChart_formulas c hc b4b_Group U C
    π hπ f ι hι hrange n hn hlocal hf.continuous hproj
  have hAt : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc c × C) :=
    fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩
  let Pa : rf7_HurwitzAtlas c b4b_Group C :=
    { hb := hc, U := U, π := π, hπ := hπ, f := f, ι := ι, hf := hf,
      hgal := hgal, hsurj := hs, hact := hG, hι := hι, hrange := hrange, hproj := hproj,
      hequiv := hequiv, total_isManifold := hm, A := A, n := n, hn := hn, hA := hAt,
      hparam := hform.1, hfree := fun q hq ↦ ⟨hunram q.2 hq, hform.2.1 q hq⟩,
      hmark := hform.2.2 }
  have slices := b6a_fibre_geometry c b4b_Group U C π f ι hc hπ hf hgal
    hs hG hι hrange hproj hequiv n hn hunram hlocal A hAt hform.1
    (fun q hq ↦ hform.2.1 q hq) hform.2.2
  choose sliceChart sliceMan hk hiSlice hg hsSlice ha _hr _hp using slices
  let e (t : b6t_polydisc c) : b65z_fibre c C t ≃ₜ C := b6m_coordinate c C t
  have pulls (t : b6t_polydisc c) :=
    @rf8_pullback_charts (b65z_fibre c C t) C _ _ (sliceChart t) (sliceMan t) (e t)
  choose fibreChart fibreMan he heinv using pulls
  let : ∀ t, ChartedSpace ℂ (b65z_fibre c C t) := fibreChart
  let : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (b65z_fibre c C t) := fibreMan
  let : ∀ t, T2Space (b65z_fibre c C t) := fun t ↦ (e t).symm.t2Space
  let : ∀ t, CompactSpace (b65z_fibre c C t) := fun t ↦ (e t).symm.compactSpace
  let : ∀ t, ConnectedSpace (b65z_fibre c C t) := fun t ↦
    (e t).symm.surjective.connectedSpace (e t).symm.continuous
  have hprojection (t : b6t_polydisc c) :
      b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t =
        (fun x : C ↦ b6a_map c f (t, x)) ∘ e t := by
    funext x
    change b6a_map c f x.val = b6a_map c f (t, x.val.2)
    exact congrArg (b6a_map c f) (Prod.ext x.property rfl)
  have hkF (t : b6t_polydisc c) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) := by
    let : ChartedSpace ℂ C := sliceChart t
    rw [hprojection]
    exact (hk t).comp (he t)
  have hiF (t : b6t_polydisc c) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b65z_fibre c C t ↦ x.val) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (hiSlice t).comp (he t) using 1
    funext x
    exact Prod.ext x.property rfl
  have hGF (t : b6t_polydisc c) (g : b4b_Group) :
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b65z_fibre c C t ↦ g • x) := by
    let : ChartedSpace ℂ C := sliceChart t
    convert (heinv t).comp ((ha t g).comp (he t)) using 1
    funext x
    rfl
  have hsF (t : b6t_polydisc c) : Function.Surjective
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) := by
    rw [hprojection]
    exact (hsSlice t).comp (e t).surjective
  have heact (t : b6t_polydisc c) (g : b4b_Group) (x : b65z_fibre c C t) :
      e t (g • x) = g • e t x := rfl
  have hgF (t : b6t_polydisc c) : b4_IsGaloisCover b4b_Group
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) := by
    refine ⟨fun g x ↦ ?_, fun x y h ↦ ?_⟩
    · rw [hprojection]
      change b6a_map c f (t, e t (g • x)) = b6a_map c f (t, e t x)
      rw [heact]
      exact (hg t).1 g (e t x)
    · rw [hprojection] at h
      obtain ⟨g, hg⟩ := (hg t).2 (e t x) (e t y) h
      exact ⟨g, (e t).injective ((heact t g x).trans hg)⟩
  let it (t : b6t_polydisc c) : U → b65z_fibre c C t := (e t).symm ∘ ι
  have hit (t : b6t_polydisc c) : Topology.IsOpenEmbedding (it t) :=
    (e t).symm.isOpenEmbedding.comp hι
  have het (t : b6t_polydisc c) (g : b4b_Group) (u : U) :
      it t (g • u) = g • it t u := rfl
  have hrt (t : b6t_polydisc c) : Set.range (it t) =
      (b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t) ⁻¹'
        (Set.range (b6_branch t.val))ᶜ := by
    ext x
    have hb := b6a_fibre_branch_preimage c hc C f t
    change (∃ u, (e t).symm (ι u) = x) ↔ _
    rw [hprojection]
    change (∃ u, (e t).symm (ι u) = x) ↔
      (e t x) ∉ (fun x : C ↦ b6a_map c f (t, x)) ⁻¹' Set.range (b6_branch t.val)
    rw [hb]
    change (∃ u, (e t).symm (ι u) = x) ↔ e t x ∈ f ⁻¹' (Set.range (b6_branch c))ᶜ
    rw [← hrange]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, ((e t).apply_symm_apply _).symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, (e t).injective (by simpa using hu)⟩
  have stabilizers (t : b6t_polydisc c) :
      FaithfulSMul b4b_Group (b65z_fibre c C t) ∧
      ∀ x, b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t x ∉
        Set.range (b6_branch t.val) → MulAction.stabilizer b4b_Group x = ⊥ := by
    obtain ⟨et, -⟩ := b6t_punctured_homeomorph c hc t.val t.property
    exact rf8_filling_stabilizers t.val U (b65z_fibre c C t) (et ∘ π)
      (hπ.homeomorph_comp et) u₀.1 _ (it t) (hit t).injective (hrt t) (het t)
  let : ∀ t, FaithfulSMul b4b_Group (b65z_fibre c C t) := fun t ↦ (stabilizers t).1
  have hrotF (t : b6t_polydisc c) : ∀ j, ∃ x : b65z_fibre c C t,
      b63d_projection c C f (b6t_polydisc c) (Set.Subset.refl _) t x =
        b6_branch t.val j ∧ b4_IsRotGen ℂ x (g j) :=
    b65z_rot_transfer c hc g t.val t.property π hπ hG f hf hgal stab₀.2 ι hι.continuous
      hproj hequiv hrot₀ (hGF t) _ (hkF t) (hgF t) (stabilizers t).2 (it t)
      (hit t).continuous (fun u ↦ by
        change b6t_sphere c t.val (f (ι u)) = _
        rw [hproj]) (het t)
  have hbranchF (t : b6t_polydisc c) := b65z_branchSet t.val g hne
    (b65z_fibre c C t) (hGF t) _ (hkF t) (hgF t) (stabilizers t).2 (hrotF t)
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (by simp)
  have hq (t : b6t_polydisc c) :=
    b3_exists_intersectionForm (C := b65z_fibre c C t) (E := ℂ) (by simp)
  choose Q hQ using hq
  choose P hP using fun t : b6t_polydisc c ↦ b6m_period_comparison (b65z_fibre c C t)
  choose Aop hAop _hsq using fun t : b6t_polydisc c ↦
    b63d_prymOperator_sq c C hC (b6t_polydisc c) (Set.Subset.refl _) t (hGF t)
  exact ⟨{ C := C
           hC := hC
           atlas := Pa
           hincl := hiF
           hG := hGF
           hk := hkF
           hsurj := hsF
           hgal := hgF
           hbranch := hbranchF
           hrot := hrotF
           Q₀ := Q₀
           hQ₀ := hQ₀
           Q := Q
           hQ := hQ
           P := fun t ↦ (P t).toLinearMap
           hP := hP
           A := Aop
           hA := hAop }, u₀, rfl⟩

end Filling

/-- A lift of a based loop from a marked point ends at the translate given by the monodromy. -/
theorem b65w_lift_end {X U G : Type} [TopologicalSpace X] [TopologicalSpace U] [Group G]
    [MulAction G U] {π : U → X} (hπ : IsQuotientCoveringMap π G) {y : X} (u : π ⁻¹' {y})
    (P : Path y y) :
    ∃ L : C(unitInterval, U), (∀ t, π (L t) = P t) ∧ L 0 = u.1 ∧
      L 1 = (hπ.fundamentalGroupToMulOpposite u (FundamentalGroup.fromPath ⟦P⟧)).unop • u.1 := by
  have hcov := hπ.isCoveringMap
  let L := hcov.liftPath P.toContinuousMap u.1 (P.source.trans u.2.symm)
  have hL := hcov.liftPath_lifts P.toContinuousMap u.1 (P.source.trans u.2.symm)
  have hL0 := hcov.liftPath_zero P.toContinuousMap u.1 (P.source.trans u.2.symm)
  refine ⟨L, fun t ↦ congrFun hL t, hL0, ?_⟩
  have h1 := hcov.monodromy_eq_apply_one (γ := P) (e := u) (Γ := L) hL hL0
  have h2 := hπ.unop_fundamentalGroupToMulOpposite_smul (e := u)
    (γ := FundamentalGroup.fromPath ⟦P⟧)
  rw [h2]
  exact h1.symm

/-- **The named family.** See `b65w_named_family`. -/
theorem b65w_named_family_core (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (hρ : Function.Surjective ρ)
    (hnamed : ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
      ∀ a : FundamentalGroup b65s_sphere (b65s_inclusion x),
        D.atlas.hπ.fundamentalGroupToMulOpposite u₀
          ((FundamentalGroup.map (⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))) (b65s_inclusion x)) a) = MulOpposite.op (ρ a)⁻¹ := by
  classical
  have hc : b65z_centre p ∈ b6_chart := ((b65p_normalized_path p hp).1.self_of_nhds).1
  obtain ⟨ψ, hψ⟩ := RiemannRochTop_homeomorph_pi1_map e (b65s_inclusion x)
  have hψmap : ∀ a, ψ a = FundamentalGroup.map ⟨e, e.continuous⟩ (b65s_inclusion x) a := by
    intro a
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep a.asHom
    have ha : a = FundamentalGroup.fromPath ⟦γ⟧ := by
      rw [show (⟦γ⟧ : Path.Homotopic.Quotient _ _) = a.asHom from hγ]
    rw [ha, hψ]
    rfl
  let φ : FundamentalGroup (b6t_punctured (b65z_centre p)) (e (b65s_inclusion x)) →*
      b4b_Groupᵐᵒᵖ :=
    (MulEquiv.inv' b4b_Group).toMonoidHom.comp (ρ.comp ψ.symm.toMonoidHom)
  have hφψ : ∀ a, φ (ψ a) = MulOpposite.op (ρ a)⁻¹ := by
    intro a
    simp [φ]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨a, ha⟩ := hρ (z.unop⁻¹)
    exact ⟨ψ a, by rw [hφψ, ha, inv_inv, MulOpposite.op_unop]⟩
  obtain ⟨U, _, _, _, π, hπ, u₀, hφeq, C₀, _, _, _, _, _, _, _, f₀, ι₀, hf₀, hgal₀, -, hG₀,
    hι₀, hιr₀, hfι₀, hιeq₀⟩ := b6m_marked_rex (b65z_centre p) hc b4b_Group _ φ hφs
  obtain ⟨hfaith₀, hstab₀⟩ := rf8_filling_stabilizers (b65z_centre p) U C₀ π hπ u₀.1 f₀ ι₀
    hι₀.injective hιr₀ hιeq₀
  have := hfaith₀
  have hY : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
    have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
    rw [h, finrank_bot]
  set b' : Fin 13 → OnePoint ℂ := b6_branch (b65z_centre p) ∘ Fin.rev with hb'def
  have hb' : Function.Injective b' := hc.comp Fin.rev_injective
  have hrange : Set.range b' = Set.range (b6_branch (b65z_centre p)) :=
    Fin.rev_surjective.range_comp _
  let y₀' : {y : OnePoint ℂ // y ∉ Set.range b'} :=
    ⟨(e (b65s_inclusion x) : OnePoint ℂ), by rw [hrange]; exact (e (b65s_inclusion x)).property⟩
  obtain ⟨γ, hγprod, huniv, hlift⟩ := b4_punctured_presentation (E := ℂ) (E' := ℂ)
    (by simp) (by simp) hY b' hb' y₀'
  let eS : {y : OnePoint ℂ // y ∉ Set.range b'} ≃ₜ b6t_punctured (b65z_centre p) :=
    Homeomorph.setCongr (congrArg compl hrange)
  let mS := FundamentalGroup.map (⟨eS, eS.continuous⟩ :
    C({y : OnePoint ℂ // y ∉ Set.range b'}, b6t_punctured (b65z_centre p))) y₀'
  let φ' : FundamentalGroup {y : OnePoint ℂ // y ∉ Set.range b'} y₀' →* b4b_Groupᵐᵒᵖ :=
    φ.comp mS
  let g : Fin 13 → b4b_Group := fun k ↦ MulOpposite.unop (φ' (γ k.rev))
  have hg_val : ∀ k, φ' (γ k.rev) = MulOpposite.op (g k) := fun k ↦ (MulOpposite.op_unop _).symm
  have hprod : (List.ofFn g).prod = 1 := by
    have h1 := map_list_prod φ' (List.ofFn γ)
    rw [hγprod, map_one, List.map_ofFn] at h1
    have h2 : List.ofFn (φ' ∘ γ) = List.ofFn (fun j ↦ MulOpposite.op (g j.rev)) := by
      congr 1
      funext j
      simp only [Function.comp_apply, g, Fin.rev_rev, MulOpposite.op_unop]
    rw [h2, HurwitzPrymRR_prod_op_rev] at h1
    exact MulOpposite.op_injective (by rw [MulOpposite.op_one]; exact h1.symm)
  have hγgen := b65w_closure_of_unique γ hγprod (fun H _ k hk ↦ huniv H k hk)
  have hmS : Function.Surjective mS := by
    obtain ⟨χ, hχ⟩ := RiemannRochTop_homeomorph_pi1_map eS y₀'
    intro b
    obtain ⟨a, rfl⟩ := χ.surjective b
    refine ⟨a, ?_⟩
    obtain ⟨γa, hγa⟩ := Quotient.exists_rep a.asHom
    have ha : a = FundamentalGroup.fromPath ⟦γa⟧ := by
      rw [show (⟦γa⟧ : Path.Homotopic.Quotient _ _) = a.asHom from hγa]
    rw [ha, hχ]
    rfl
  have hφ's : Function.Surjective φ' := hφs.comp hmS
  have hgen : Subgroup.closure (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, ha⟩ := hφ's (MulOpposite.op z)
    have key : ∀ a ∈ Subgroup.closure (Set.range γ),
        (φ' a).unop ∈ Subgroup.closure (Set.range g) := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        have : (φ' (γ j)).unop = g j.rev := by simp only [g, Fin.rev_rev]
        rw [this]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      | one => rw [map_one, MulOpposite.unop_one]; exact Subgroup.one_mem _
      | mul x y _ _ hx hy =>
        rw [map_mul, MulOpposite.unop_mul]
        exact Subgroup.mul_mem _ hy hx
      | inv x _ hx =>
        rw [map_inv, MulOpposite.unop_inv]
        exact Subgroup.inv_mem _ hx
    have := key a (by rw [hγgen]; trivial)
    rwa [ha, MulOpposite.unop_op] at this
  have hpos : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
      [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
      [FaithfulSMul b4b_Group C],
      (∀ k : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x)) →
      ∀ f : C → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover b4b_Group f →
      (∀ x, f x ∉ Set.range (b6_branch (b65z_centre p)) →
        MulAction.stabilizer b4b_Group x = ⊥) →
      ∀ ι : U → C, Continuous ι → (∀ u, f (ι u) = π u) →
      (∀ (k : b4b_Group) (u : U), ι (k • u) = k • ι u) →
      ∀ j, ∃ x, f x = b6_branch (b65z_centre p) j ∧ b4_IsRotGen ℂ x (g j) := by
    intro C _ _ _ _ _ _ _ _ hG f hf hgal hfree ι hι hfι hιeq j
    have hfree' : ∀ x, f x ∉ Set.range b' → MulAction.stabilizer b4b_Group x = ⊥ := by
      rw [hrange]; exact hfree
    obtain ⟨P, hP⟩ := Quotient.exists_rep (FundamentalGroup.toPath (γ j.rev))
    have hPc : FundamentalGroup.fromPath ⟦P⟧ = γ j.rev := by
      rw [hP]
    obtain ⟨L, hLπ, hL0, hL1⟩ := b65w_lift_end hπ u₀ (P.map eS.continuous)
    have hμ : hπ.fundamentalGroupToMulOpposite u₀
        (FundamentalGroup.fromPath ⟦P.map eS.continuous⟧) = MulOpposite.op (g j) := by
      rw [hφeq, ← hg_val j, ← hPc]
      rfl
    rw [hμ, MulOpposite.unop_op] at hL1
    obtain ⟨y, hy, hrot⟩ := hlift C b4b_Group hG f hf hgal hfree' j.rev P hPc
      ⟨ι ∘ L, hι.comp L.continuous⟩ (g j) (fun t ↦ by
        simp only [ContinuousMap.coe_mk, Function.comp_apply, hfι, hLπ]
        rfl)
      (by
        simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hιeq, hL0])
    refine ⟨y, ?_, hrot⟩
    rw [hy]
    simp [b']
  have hslot : ∀ i, ∃ q, f₀ q = b6_branch (b65z_centre p) (b65x_slot i).rev ∧
      b4_IsRotGen ℂ q (b65b_initial i)⁻¹ := by
    intro i
    obtain ⟨L, hLπ, hL0, hL1⟩ := b65w_lift_end hπ u₀
      (((δ i).map b65s_inclusion.continuous).map e.continuous)
    have hμ : hπ.fundamentalGroupToMulOpposite u₀ (FundamentalGroup.fromPath
        ⟦((δ i).map b65s_inclusion.continuous).map e.continuous⟧) =
          MulOpposite.op (b65b_initial i)⁻¹ := by
      rw [hφeq, ← hψ, hφψ]
      exact congrArg (fun z ↦ MulOpposite.op z⁻¹) (hnamed i)
    rw [hμ, MulOpposite.unop_op] at hL1
    exact b65w_slot_rotGen p hp e he x δ hδ i hG₀ f₀ hf₀ hgal₀ hstab₀
      ⟨ι₀ ∘ L, hι₀.continuous.comp L.continuous⟩ (b65b_initial i)⁻¹
      (fun t ↦ by
        simp only [ContinuousMap.coe_mk, Function.comp_apply, hfι₀, hLπ]
        rfl)
      (by simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hιeq₀, hL0])
  have hslotb : Function.Bijective b65x_slot := by decide
  let sE : Equiv.Perm (Fin 13) := Equiv.ofBijective b65x_slot hslotb
  let τ : Equiv.Perm (Fin 13) := Fin.revPerm.trans sE.symm
  have hτ : ∀ j, (b65x_slot (τ j)).rev = j := by
    intro j
    have : b65x_slot (τ j) = j.rev := by
      change sE (sE.symm (Fin.revPerm j)) = j.rev
      rw [Equiv.apply_symm_apply]
      rfl
    rw [this, Fin.rev_rev]
  have hconj : ∀ j, IsConj (g j) (b65b_initial (τ j))⁻¹ := by
    intro j
    obtain ⟨x₁, hx₁, hr₁⟩ := hpos C₀ hG₀ f₀ hf₀ hgal₀ hstab₀ ι₀ hι₀.continuous hfι₀ hιeq₀ j
    obtain ⟨x₂, hx₂, hr₂⟩ := hslot (τ j)
    rw [hτ] at hx₂
    obtain ⟨h, hh⟩ := b65z_rotGen_conj hG₀ f₀ hgal₀ x₁ x₂ (hx₁.trans hx₂.symm) (g j)
      (b65b_initial (τ j))⁻¹ hr₁ hr₂
    exact isConj_iff.mpr ⟨h, hh.symm⟩
  have hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := b65w_nielsen g hprod hgen τ hconj
  obtain ⟨D, u, hDu⟩ := b65w_family_of_cover (b65z_centre p) hc g (b65z_nielsen_ne_one g hg)
    U π hπ hpos _ u₀
  refine ⟨g, hg, D, u, fun a ↦ ?_⟩
  rw [hDu, hφeq, ← hψmap, hφψ]

end HodgeLean.Foundations.Program
