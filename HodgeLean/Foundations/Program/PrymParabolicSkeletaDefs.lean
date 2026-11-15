import HodgeLean.Foundations.Program.PrymParabolicSimplices
import HodgeLean.Foundations.Program.PrymParabolicSaturated

/-! # Definitions for stage H3b step C, first part: skeleta and the degree-one comparison

Step B (`PrymParabolicSimplices.lean`) gives, for a family `L` of lifts of the base triangles of
G32 Figure 1 to the filling `C` of the marked root cover, singular simplices of `C` whose faces
and endpoints follow the incidences of the lifted complex `X̃(g)` of stage H3a
(`hg5_lift_faces`, `hg5_lift_vertices`). This file packages such data as a `Δ`-map from `X̃(g)`
into the singular simplicial set of a space (`hg8_DeltaMap`) and defines, for any `Δ`-map:

- the cellular-to-singular map on cycles and the induced map `hg2_H1 ℤ g →ₗ[ℤ] b6m_H1 T`
  (`hg8_H1map`), with the identification of the two singular models used
  (`hg8_modelEquiv`: the homology of the chain complex of `TopCat.toSSet` and `b6m_H1`);
- the closed skeleta `T⁰ = range vert` and `T¹ = T⁰ ∪ ⋃ range edge` and the pairs
  `(T¹, T⁰)`, `(T, T¹)`;
- the class of a relative cycle in relative singular homology (`hg8_relClass`), the cellular
  bases `hg8_vertClass`, `hg8_edgeRel`, `hg8_triRel` of `H₀(T⁰)`, `H₁(T¹, T⁰)`, `H₂(T, T¹)`;
- the connecting maps of the pairs and the projection `H₁(T¹) → H₁(T¹, T⁰)`.

Two instances: the base decomposition of the sphere (`hg8_baseMap`, trivial group) and the
lifted cells (`hg8_liftMap`, built from the step-B theorems, which have bodies).

Nothing here computes a relative group, identifies a connecting map, or compares cellular and
singular homology; those are the statements of `PrymParabolicSkeleta.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Convexity

namespace HodgeLean.Foundations.Program

/-! ## `Δ`-maps from the lifted complex -/

/-- A `Δ`-map from the lifted complex `X̃(g)` into the singular simplicial set of `T`: a
singular `2`-simplex for each triangle, a path for each edge and a point for each vertex, such
that the faces `0, 1, 2` of each triangle are the edges named by `hg2_face0/1/2` and each edge
runs from the vertex `hg2_src` to the vertex `hg2_tgt`.
Source: Hatcher, *Algebraic Topology*, §2.1 (Δ-complexes and their singular simplices);
G32 v0.16, Figure 1; `hg2_face0/1/2`, `hg2_src`, `hg2_tgt`. -/
structure hg8_DeltaMap {G : Type} [Group G] {r : ℕ} (g : Fin r → G) (T : Type)
    [TopologicalSpace T] where
  /-- The singular triangle of each cell `A_i(x)`, `B_i(x)`. -/
  tri : hg2_Tri G r → C(StdSimplex ℝ (Fin 3), T)
  /-- The path of each edge `e_i(x)`, `f_i(x)`, `h_i(x)`. -/
  edge : hg2_Edge G r → C(unitInterval, T)
  /-- The point of each vertex. -/
  vert : hg2_Vert g → T
  faces : ∀ τ, hg5_face (tri τ) 0 = edge (hg2_face0 g τ) ∧
    hg5_face (tri τ) 1 = edge (hg2_face1 τ) ∧ hg5_face (tri τ) 2 = edge (hg2_face2 τ)
  ends : ∀ ε, edge ε 0 = vert (hg2_src g ε) ∧ edge ε 1 = vert (hg2_tgt g ε)

/-- The base decomposition of the sphere at `mr_base` as a `Δ`-map from `X̃` of the trivial
tuple.
Source: `hg5_faces`, `hg5_edge_ends` (step A, with bodies). -/
def hg8_baseMap : hg8_DeltaMap hg5_one (OnePoint ℂ) :=
  ⟨hg5_tri, hg5_edge, hg5_vert, hg5_faces, hg5_edge_ends⟩

example : hg8_baseMap.tri = hg5_tri := rfl

/-- The lifted cells of step B as a `Δ`-map from `X̃(g)` into the filling `C`: the triangles
`L τ`, the edges `hg5_liftEdge L` and the vertices `hg5_liftVert g L`. The binders are those of
`hg5_lift_chain1`.
Source: `hg5_lift_faces`, `hg5_lift_vertices` (step B, with bodies). -/
def hg8_liftMap {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction G C]
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
    hg8_DeltaMap g C :=
  ⟨L, hg5_liftEdge L, hg5_liftVert g L,
    hg5_lift_faces U π hπ y₀ hy₀ u₀ g γ hγ hroot C f hf ι hι hιr hfι hιG L hL,
    (hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι
      hιG L hL).1⟩

/-! ## The induced map on `H₁` -/

/-- The singular chain complex of `TopCat.toSSet` (in which the step-B chains live) and Mathlib's
`SingularChainComplex` are the same complex, so their degree-one homologies are equal; this is
that identification as a linear equivalence.
Source: Mathlib `AlgebraicTopology.singularChainComplexFunctor` (defined as
`TopCat.toSSet ⋙ SSet.chainComplexFunctor`); `b6m_H1`. -/
def hg8_modelEquiv (T : Type) [TopologicalSpace T] :
    ((TopCat.toSSet.obj (TopCat.of T)).chainComplex (ModuleCat.of ℤ ℤ)).homology 1 ≃ₗ[ℤ]
      b6m_H1 T :=
  LinearEquiv.refl ℤ _

example (T : Type) [TopologicalSpace T] (x : b6m_H1 T) : hg8_modelEquiv T x = x := rfl

theorem hg8_d_chain1_eq_zero {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (z : hg2_Edge G r →₀ ℤ)
    (hz : z ∈ LinearMap.ker (hg2_bd1 ℤ g)) (j : ℕ) :
    ((SingularChainComplex ℤ (TopCat.of T)).d 1 j).hom (hg5_chain1 F.edge z) = 0 := by
  by_cases hj : j = 0
  · subst hj
    change Simplicial.boundary ℤ 0 (hg5_chain1 F.edge z) = 0
    rw [hg5_bd_chain1 F.edge F.vert _ _ F.ends z]
    change hg5_chain0 F.vert (hg2_bd1 ℤ g z) = 0
    rw [LinearMap.mem_ker.mp hz, map_zero]
  · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
    rfl

/-- The cellular-to-singular map on `1`-cycles: a cellular cycle `z` goes to the singular
cycle `Σ z(ε) [edge ε]`.
Source: Hatcher, *Algebraic Topology*, §2.1 (a chain map sends cycles to cycles);
`hg5_chain1`, `hg5_bd_chain1`. -/
def hg8_cycle1 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) :=
  LinearMap.restrict (hg5_chain1 F.edge :
      (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] ((SingularChainComplex ℤ (TopCat.of T)).sc 1).X₂)
    (p := LinearMap.ker (hg2_bd1 ℤ g))
    (q := LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom)
    (fun z hz ↦ hg8_d_chain1_eq_zero F z hz _)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    (hg8_cycle1 F z).1 = hg5_chain1 F.edge z.1 := rfl

theorem hg8_homologyClass_eq_zero {R : Type} [CommRing R] (S : ShortComplex (ModuleCat.{0} R))
    (w : LinearMap.ker S.g.hom) (h : w.1 ∈ LinearMap.range S.f.hom) :
    S.moduleCatHomologyClass w = 0 := by
  have hq : (LinearMap.range S.moduleCatToCycles).mkQ w = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨a, ha⟩ := h
    exact ⟨a, Subtype.ext ha⟩
  exact (congrArg S.moduleCatHomologyIso.inv.hom hq).trans (map_zero _)

/-- The class of a boundary is zero, with the boundary written through `d (i + 1) i`. -/
theorem hg8_class_eq_zero_of_d {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) (i : ℕ)
    (w : LinearMap.ker (K.sc i).g.hom) (a : K.X (i + 1)) (h : (K.d (i + 1) i).hom a = w.1) :
    (K.sc i).moduleCatHomologyClass w = 0 := by
  apply hg8_homologyClass_eq_zero
  have hp : (ComplexShape.down ℕ).prev i = i + 1 := ChainComplex.prev ℕ i
  refine ⟨(K.XIsoOfEq hp).inv.hom a, ?_⟩
  change (K.d ((ComplexShape.down ℕ).prev i) i).hom ((K.XIsoOfEq hp).inv.hom a) = w.1
  rw [← HomologicalComplex.XIsoOfEq_hom_comp_d K hp, ModuleCat.hom_comp, LinearMap.comp_apply,
    ← LinearMap.comp_apply (K.XIsoOfEq hp).hom.hom, ← ModuleCat.hom_comp, Iso.inv_hom_id]
  exact h

theorem hg8_cycle1_boundary {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (z : LinearMap.ker (hg2_bd1 ℤ g))
    (hz : z ∈ (LinearMap.range (hg2_bd2 ℤ g)).comap (LinearMap.ker (hg2_bd1 ℤ g)).subtype) :
    ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (hg8_cycle1 F z) = 0 := by
  obtain ⟨w, hw⟩ := hz
  refine hg8_class_eq_zero_of_d _ 1 _ (hg5_chain2 F.tri w) ?_
  change Simplicial.boundary ℤ 1 (hg5_chain2 F.tri w) = hg5_chain1 F.edge z.1
  rw [hg5_bd_chain2 F.tri F.edge _ _ _ F.faces w]
  change hg5_chain1 F.edge (hg2_bd2 ℤ g w) = _
  rw [hw]
  rfl

/-- The map `hg2_H1 ℤ g →ₗ[ℤ] b6m_H1 T` induced by a `Δ`-map: the class of a cellular cycle goes
to the singular class of its image. Cellular boundaries go to singular boundaries by the face
compatibility (`hg5_bd_chain2`).
Source: Hatcher, *Algebraic Topology*, §2.1 (induced maps on homology); `hg2_H1`, `b6m_H1`. -/
def hg8_H1map {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : hg2_H1 ℤ g →ₗ[ℤ] b6m_H1 T :=
  Submodule.liftQ _
    (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass ∘ₗ hg8_cycle1 F)
    (fun z hz ↦ hg8_cycle1_boundary F z hz)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    hg8_H1map F (Submodule.Quotient.mk z) =
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (hg8_cycle1 F z) :=
  rfl

/-! ## Naturality of the cellular-to-singular maps -/

/-- The singular chain map of a continuous map `φ : A → B` in degree `n`.
Source: Hatcher, *Algebraic Topology*, §2.1 (induced chain maps); `SSet.chainComplexMap`. -/
abbrev hg8_chainMap {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    (n : ℕ) : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of A)) n →ₗ[ℤ]
      Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of B)) n :=
  ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom φ)) (ModuleCat.of ℤ ℤ)).f n).hom

example {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B)) (n : ℕ) :
    hg8_chainMap φ n 0 = 0 := map_zero _

theorem hg8_chain0_map {ι A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    (v : ι → A) (c : ι →₀ ℤ) :
    hg8_chainMap φ 0 (hg5_chain0 v c) = hg5_chain0 (φ ∘ v) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | single x n =>
    simp only [hg5_chain0, Finsupp.linearCombination_single]
    erw [LinearMap.map_smul]
    congr 1
    exact Simplicial.chainOfSimplex_map ℤ (TopCat.toSSet.map (TopCat.ofHom φ)) _

theorem hg8_chain1_map {ι A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    (e : ι → C(unitInterval, A)) (c : ι →₀ ℤ) :
    hg8_chainMap φ 1 (hg5_chain1 e c) = hg5_chain1 (fun x ↦ φ.comp (e x)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | single x n =>
    simp only [hg5_chain1, Finsupp.linearCombination_single]
    erw [LinearMap.map_smul]
    congr 1
    exact Simplicial.chainOfSimplex_map ℤ (TopCat.toSSet.map (TopCat.ofHom φ)) _

/-! ## Skeleta and pairs -/

/-- The `0`-skeleton `T⁰` of a `Δ`-map: the points of the vertices.
Source: Hatcher, *Algebraic Topology*, §2.1 and §2.2 (skeleta of a Δ-complex). -/
def hg8_skel0 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : Set T :=
  Set.range F.vert

example : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ hg8_skel0 hg8_baseMap := ⟨Sum.inl (), rfl⟩

/-- The `1`-skeleton `T¹ = T⁰ ∪ ⋃_ε edge ε ([0, 1])`.
Source: Hatcher, *Algebraic Topology*, §2.1 and §2.2 (skeleta of a Δ-complex). -/
def hg8_skel1 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : Set T :=
  hg8_skel0 F ∪ ⋃ ε, Set.range (F.edge ε)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : hg8_skel0 F ⊆ hg8_skel1 F := Set.subset_union_left

/-- A vertex as a point of `T¹`.
Source: `hg8_skel1`; Mathlib `Subtype`. -/
def hg8_vert1 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (v : hg2_Vert g) : hg8_skel1 F :=
  ⟨F.vert v, Or.inl ⟨v, rfl⟩⟩

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (v : hg2_Vert g) : (hg8_vert1 F v : T) = F.vert v := rfl

/-- A vertex as a point of `T⁰ ⊆ T¹` (the subspace of the pair `(T¹, T⁰)`).
Source: `hg8_skel0`, `hg8_skel1`; Mathlib `Subtype`. -/
def hg8_vert0 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (v : hg2_Vert g) :
    (Subtype.val ⁻¹' hg8_skel0 F : Set (hg8_skel1 F)) :=
  ⟨hg8_vert1 F v, ⟨v, rfl⟩⟩

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (v : hg2_Vert g) : ((hg8_vert0 F v : hg8_skel1 F) : T) = F.vert v :=
  rfl

/-- An edge as a path in `T¹`.
Source: `hg8_skel1`; Mathlib `ContinuousMap.codRestrict`. -/
def hg8_edge1 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (ε : hg2_Edge G r) : C(unitInterval, hg8_skel1 F) :=
  ⟨fun s ↦ ⟨F.edge ε s, Or.inr (Set.mem_iUnion.mpr ⟨ε, s, rfl⟩)⟩, by fun_prop⟩

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (ε : hg2_Edge G r) (s : unitInterval) :
    (hg8_edge1 F ε s : T) = F.edge ε s := rfl

/-- The pair `(T¹, T⁰)`.
Source: Hatcher, *Algebraic Topology*, §2.1 (relative homology); `TopPair.ofSubset`. -/
abbrev hg8_pair10 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (hg8_skel1 F)) (Subtype.val ⁻¹' hg8_skel0 F)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : (hg8_pair10 F).fst = TopCat.of (hg8_skel1 F) := rfl

/-- The pair `(T, T¹)`.
Source: Hatcher, *Algebraic Topology*, §2.1 (relative homology); `TopPair.ofSubset`. -/
abbrev hg8_pair21 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of T) (hg8_skel1 F)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : (hg8_pair21 F).fst = TopCat.of T := rfl

/-! ## Relative cycles and their classes -/

/-- The relative `(n + 1)`-cycles of a pair `(X, A)`, as absolute chains: chains of `X` whose
boundary is a chain of `A`.
Source: Hatcher, *Algebraic Topology*, §2.1 (relative cycles). -/
def hg8_relCycles (R : Type) [CommRing R] (P : TopPair.{0}) (n : ℕ) :
    Submodule R ((SingularChainComplex R P.fst).X (n + 1)) :=
  (LinearMap.range (((chainPairFunctor R).obj P).hom.f n).hom).comap
    ((SingularChainComplex R P.fst).d (n + 1) n).hom

example (R : Type) [CommRing R] (P : TopPair.{0}) (n : ℕ) :
    (0 : (SingularChainComplex R P.fst).X (n + 1)) ∈ hg8_relCycles R P n :=
  Submodule.zero_mem _

theorem hg8_relCycles_d (R : Type) [CommRing R] (P : TopPair.{0}) (n : ℕ)
    (c : (SingularChainComplex R P.fst).X (n + 1)) (hc : c ∈ hg8_relCycles R P n) (j : ℕ) :
    (((relativeChainFunctor R).obj P).d (n + 1) j).hom
      (((relativeChainProjection R P).f (n + 1)).hom c) = 0 := by
  by_cases hj : j = n
  · subst hj
    obtain ⟨a, ha⟩ := hc
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (relativeChainProjection R P).comm,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← ha]
    have h0 : ((((chainPairFunctor R).obj P).hom ≫ relativeChainProjection R P).f j).hom a = 0 := by
      rw [subspaceChainMap_relativeChainProjection]; rfl
    exact h0
  · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
    rfl

/-- The class in `H_{n+1}(X, A)` of a relative cycle.
Source: Hatcher, *Algebraic Topology*, §2.1 (relative homology classes);
`relativeChainProjection`. -/
def hg8_relClass (R : Type) [CommRing R] (P : TopPair.{0}) (n : ℕ) :=
  (((relativeChainFunctor R).obj P).sc (n + 1)).moduleCatHomologyClass ∘ₗ
    LinearMap.restrict ((relativeChainProjection R P).f (n + 1)).hom
      (p := hg8_relCycles R P n)
      (q := LinearMap.ker (((relativeChainFunctor R).obj P).sc (n + 1)).g.hom)
      (fun c hc ↦ hg8_relCycles_d R P n c hc _)

example (R : Type) [CommRing R] (P : TopPair.{0}) (n : ℕ) :
    hg8_relClass R P n 0 = 0 := map_zero _

/-! ## The cellular bases of the skeletal groups -/

theorem hg8_d_zero_eq_zero (X : TopCat.{0}) (c : (SingularChainComplex ℤ X).X 0) (j : ℕ) :
    ((SingularChainComplex ℤ X).d 0 j).hom c = 0 := by
  rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
  rfl

/-- The classes of the vertices in `H₀(T⁰)`: `v ↦ [vert v]`, extended linearly.
Source: Hatcher, *Algebraic Topology*, §2.1 (`H₀` of a space; points as `0`-cycles). -/
def hg8_vertClass {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) :=
  ((SingularChainComplex ℤ (hg8_pair10 F).snd).sc 0).moduleCatHomologyClass ∘ₗ
    LinearMap.codRestrict (LinearMap.ker ((SingularChainComplex ℤ (hg8_pair10 F).snd).sc 0).g.hom)
      (hg5_chain0 (hg8_vert0 F) :
        (hg2_Vert g →₀ ℤ) →ₗ[ℤ] ((SingularChainComplex ℤ (hg8_pair10 F).snd).sc 0).X₂)
      (fun _ ↦ hg8_d_zero_eq_zero _ _ _)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : hg8_vertClass F 0 = 0 := map_zero _

theorem hg8_edge_relCycle {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (c : hg2_Edge G r →₀ ℤ) :
    (hg5_chain1 (hg8_edge1 F) c : (SingularChainComplex ℤ (hg8_pair10 F).fst).X (0 + 1)) ∈
      hg8_relCycles ℤ (hg8_pair10 F) 0 := by
  have hends : ∀ ε, hg8_edge1 F ε 0 = hg8_vert1 F (hg2_src g ε) ∧
      hg8_edge1 F ε 1 = hg8_vert1 F (hg2_tgt g ε) :=
    fun ε ↦ ⟨Subtype.ext (F.ends ε).1, Subtype.ext (F.ends ε).2⟩
  refine ⟨hg5_chain0 (hg8_vert0 F) (hg2_bd1 ℤ g c), ?_⟩
  change hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 0
      (hg5_chain0 (hg8_vert0 F) (hg2_bd1 ℤ g c)) =
    Simplicial.boundary ℤ 0 (hg5_chain1 (hg8_edge1 F) c)
  rw [hg8_chain0_map, hg5_bd_chain1 (hg8_edge1 F) (hg8_vert1 F) _ _ hends c]
  rfl

/-- The classes of the edges in `H₁(T¹, T⁰)`: `ε ↦ [edge ε]`, a relative cycle since its
endpoints are vertices.
Source: Hatcher, *Algebraic Topology*, §2.2 (cellular chains as relative homology of skeleta,
Lemma 2.34). -/
def hg8_edgeRel {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) :=
  hg8_relClass ℤ (hg8_pair10 F) 0 ∘ₗ
    LinearMap.codRestrict (hg8_relCycles ℤ (hg8_pair10 F) 0)
      (hg5_chain1 (hg8_edge1 F) :
        (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] (SingularChainComplex ℤ (hg8_pair10 F).fst).X (0 + 1))
      (hg8_edge_relCycle F)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : hg8_edgeRel F 0 = 0 := map_zero _

theorem hg8_tri_relCycle {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T) (c : hg2_Tri G r →₀ ℤ) :
    (hg5_chain2 F.tri c : (SingularChainComplex ℤ (hg8_pair21 F).fst).X (1 + 1)) ∈
      hg8_relCycles ℤ (hg8_pair21 F) 1 := by
  refine ⟨hg5_chain1 (hg8_edge1 F) (hg2_bd2 ℤ g c), ?_⟩
  change hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 1
      (hg5_chain1 (hg8_edge1 F) (hg2_bd2 ℤ g c)) =
    Simplicial.boundary ℤ 1 (hg5_chain2 F.tri c)
  rw [hg8_chain1_map, hg5_bd_chain2 F.tri F.edge _ _ _ F.faces c]
  rfl

/-- The classes of the triangles in `H₂(T, T¹)`: `τ ↦ [tri τ]`, a relative cycle since its faces
are edges.
Source: Hatcher, *Algebraic Topology*, §2.2 (Lemma 2.34; characteristic maps of `2`-cells). -/
def hg8_triRel {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) :=
  hg8_relClass ℤ (hg8_pair21 F) 1 ∘ₗ
    LinearMap.codRestrict (hg8_relCycles ℤ (hg8_pair21 F) 1)
      (hg5_chain2 F.tri :
        (hg2_Tri G r →₀ ℤ) →ₗ[ℤ] (SingularChainComplex ℤ (hg8_pair21 F).fst).X (1 + 1))
      (hg8_tri_relCycle F)

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) : hg8_triRel F 0 = 0 := map_zero _

/-! ## Connecting maps and the projection to relative homology -/

/-- The connecting map `H_{n+1}(X, A) → H_n(A)` of the long exact sequence of a pair.
Source: Hatcher, *Algebraic Topology*, §2.1 (the long exact sequence of a pair);
`relativeChainShortComplex_shortExact`. -/
def hg8_delta (P : TopPair.{0}) (n : ℕ) :
    RelativeHomology ℤ P (n + 1) →ₗ[ℤ] Homology ℤ P.snd n :=
  ((relativeChainShortComplex_shortExact ℤ P).δ (n + 1) n (by simp)).hom

example (P : TopPair.{0}) (n : ℕ) : hg8_delta P n 0 = 0 := map_zero _

/-- The projection `H_n(X) → H_n(X, A)`.
Source: Hatcher, *Algebraic Topology*, §2.1; `relativeHomologyProjection`. -/
def hg8_proj (P : TopPair.{0}) (n : ℕ) : Homology ℤ P.fst n →ₗ[ℤ] RelativeHomology ℤ P n :=
  (relativeHomologyProjection ℤ P n).hom

example (P : TopPair.{0}) (n : ℕ) : hg8_proj P n 0 = 0 := map_zero _

end HodgeLean.Foundations.Program
