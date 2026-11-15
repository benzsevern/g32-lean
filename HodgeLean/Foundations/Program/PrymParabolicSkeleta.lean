import HodgeLean.Foundations.Program.PrymParabolicSkeletaProofs

/-! # Stage H3b step C, first part: skeleta, skeletal relative homology and the degree-one comparison (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h3c2.md` (`docs/specs/PrymParabolicSkeleta.md`).
Each theorem restates the matching `_aux` theorem in `PrymParabolicSkeletaProofs.lean`.

**Claimed (once the bodies are proved).** For any `Δ`-map from the lifted complex `X̃(g)` into a
space (`hg8_DeltaMap`): the skeleta are finite and closed (finite group, Hausdorff target), the
vertex classes are a basis of `H₀(T⁰)` (injective vertices), and the connecting maps of the
pairs `(T¹, T⁰)` and `(T, T¹)` are the cellular boundaries `∂₁`, `∂₂` on the cellular bases.
For the lifted cells of step B on the compact filling `C` of a cover of the shape of
`mr_rootCover` (`hg8_liftMap`): the complements of the skeleta are the open cells; the lifted
edges are embedded arcs with disjoint interiors; the lifted triangles are characteristic maps of
`2`-cells attached along `C¹`; `H_*(C¹, C⁰)` is free on the edges in degree `1` and zero
otherwise; `H_*(C, C¹)` is free on the triangles in degree `2` and zero otherwise; the induced
map `hg8_H1map : hg2_H1 ℤ g → b6m_H1 C` is bijective and deck-equivariant.

Checks with bodies: the lifted `Δ`-map has the step-B cells; toward step D, the comparison
carries `hg2_projector` to `b63l_homologyOperator` and the exact image of one onto the exact
image of the other (`hg8_projector_check`); the chain check toward stage H5
(`hg8_parameterLattice_check`: transported to every parameter fibre of `mr_base`, the comparison
is an equivalence of the shape `hg6_parameterLattice_transport` quantifies over, and carries
`hg6_cellLattice` onto `b63l_parameterLattice`; derived from the statements); the joint
satisfiability of all binders, including the family of lifts, for `b4b_root`; non-degeneracy
(the boundaries `∂₁`, `∂₂` of `X̃(b4b_root)` are nonzero, the base vertices are injective, the
source of the comparison contains a rank-`12` lattice).

Each statement is an implication from its binders. The cover binders are the conclusions of
`mr_rootCover` at `mr_base`; the family `L` is witnessed by `hg5_lift_existsUnique` (with a body).

**Not claimed.** The rest of step D as separate statements: the restricted comparison of the
projected lattices and its centre-only equivariance (the derived checks give the ambient
intertwining, the exact images and, through H5's statement 3, the saturated lattices). Lifts and the comparison at configurations other than `mr_base`
except through the product family of `b6m_Fibre`; any statement about intersection forms or
orientations (H4). HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- **Finite closed skeleta.** For a finite group and a Hausdorff target, the `0`-skeleton of a
`Δ`-map from `X̃(g)` is a finite closed set and the `1`-skeleton is closed: `T⁰` is the image
of the finite vertex set, `T¹` the union of `T⁰` and finitely many compact paths.
Source: Hatcher, *Algebraic Topology*, §2.1; Munkres, *Topology*, Theorems 26.3 and 26.5
(compact subsets of Hausdorff spaces are closed; continuous images of compact sets are compact). -/
theorem hg8_skel_closed {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    [T2Space T] (F : hg8_DeltaMap g T) :
    (hg8_skel0 F).Finite ∧ IsClosed (hg8_skel0 F) ∧ IsClosed (hg8_skel1 F) :=
  hg8_skel_closed_aux F

example {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    [T2Space T] (F : hg8_DeltaMap g T) :
    (hg8_skel0 F).Finite ∧ IsClosed (hg8_skel0 F) ∧ IsClosed (hg8_skel1 F) :=
  hg8_skel_closed F

/-- **The skeleta of the lifted cells.** For the lifted cells on the filling `C`, the complement
of `C¹` is the union of the open lifted triangles, and `C¹ ∖ C⁰` is the union of the open lifted
edges. The open cells avoid the lower skeleta because their images under `f` are open base cells
(`hg5_open_cells`); every point of `C` lies on a lifted triangle (`hg5_lift_cells`), on a face
of it when the barycentric point is on the boundary.
Source: `hg5_open_cells`, `hg5_lift_cells`, `hg5_lift_faces`; Hatcher, §2.1 (open simplices of
a Δ-complex). -/
theorem hg8_skel_cells {G : Type} [Group G] [Finite G]
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
        ⋃ ε, hg5_liftEdge L ε '' Set.Ioo 0 1 :=
  hg8_skel_cells_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example {G : Type} [Group G] [Finite G]
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
        ⋃ ε, hg5_liftEdge L ε '' Set.Ioo 0 1 :=
  hg8_skel_cells U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **Lifted edges are embedded arcs with disjoint interiors.** Each lifted edge is a closed
embedding of `[0, 1]` into `C`; two interior points of lifted edges coincide only on the same
edge at the same parameter; an interior point of a lifted edge is not a lifted vertex.
`f ∘ edge` is the base edge, which is injective by `hg5_open_cells` and `hg5_edge_ends`; two
lifts of one base path meeting at an interior point agree on the part of the path in the
punctured sphere (`hg5_edge_marks`), so their free end vertices `b₀(x)` or `b_∞(y)` agree, and
the labels agree because the deck action off the marks is free.
Source: `hg5_open_cells`, `hg5_edge_marks`, `hg5_lift_vertices`; Hatcher, Proposition 1.34
(uniqueness of lifts). -/
theorem hg8_edge_embed {G : Type} [Group G] [Finite G]
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
        ∀ v, hg5_liftEdge L ε s ≠ hg5_liftVert g L v) :=
  hg8_edge_embed_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example {G : Type} [Group G] [Finite G]
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
        ∀ v, hg5_liftEdge L ε s ≠ hg5_liftVert g L v) :=
  hg8_edge_embed U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **Triangle attachment and topology.** Each lifted triangle is a closed embedding of the
standard `2`-simplex into `C` (its composite with `f` is the injective base triangle,
`hg5_tri_injective`); the image of the open simplex is open in `C` (the open base triangle is an
open disc in the punctured sphere, over which the covering is trivial, and the open lifted
triangle is one sheet); the boundary of the simplex goes into `C¹` (`hg5_lift_faces`). So `L τ`
is a characteristic map of a `2`-cell of `C` attached along `C¹`.
Source: `hg5_tri_injective`, `hg5_open_cells`, `hg5_lift_faces`; Hatcher, Proposition 1.33 and
§0 (cell attachment); Brouwer's invariance of domain (Hatcher, Theorem 2B.3). -/
theorem hg8_tri_attach {G : Type} [Group G] [Finite G]
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
      L τ '' {a : StdSimplex ℝ (Fin 3) | ∀ k, 0 < a.weights k}ᶜ ⊆ hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) :=
  hg8_tri_attach_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example {G : Type} [Group G] [Finite G]
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
      L τ '' {a : StdSimplex ℝ (Fin 3) | ∀ k, 0 < a.weights k}ᶜ ⊆ hg8_skel1 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) :=
  hg8_tri_attach U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **`H₀` of the `0`-skeleton.** For a finite group, a Hausdorff target and injective vertices,
the classes of the vertices form a basis of `H₀(T⁰; ℤ)`: `T⁰` is a finite discrete space and
the vertex map is a bijection onto it.
Source: Hatcher, *Algebraic Topology*, Proposition 2.6 and Proposition 2.7 (`H₀` of a space is
free on its path components). -/
theorem hg8_vertClass_bijective {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    [T2Space T] (F : hg8_DeltaMap g T)
    (hinj : Function.Injective F.vert) :
    Function.Bijective (hg8_vertClass F) :=
  hg8_vertClass_bijective_aux F hinj

example {G : Type} [Group G] [Finite G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    [T2Space T] (F : hg8_DeltaMap g T)
    (hinj : Function.Injective F.vert) :
    Function.Bijective (hg8_vertClass F) :=
  hg8_vertClass_bijective F hinj

/-- **The edge calculation.** For the lifted cells, the edge classes form a basis of
`H₁(C¹, C⁰; ℤ)`, and `H_n(C¹, C⁰; ℤ) = 0` for `n ≠ 1`: by excision to a neighbourhood of the
open edges (`b6m_openCover_relativeChainMap_quasiIso`) the pair splits into the pairs
`([0, 1], {0, 1})` of the embedded arcs of `hg8_edge_embed`.
Source: Hatcher, *Algebraic Topology*, Lemma 2.34(a) and Proposition 2.22 (good pairs);
Theorem 2.20 (excision). -/
theorem hg8_edgeRel_bijective {G : Type} [Group G] [Finite G]
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
      ∀ n, n ≠ 1 → Subsingleton (RelativeHomology ℤ (hg8_pair10 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) n) :=
  hg8_edgeRel_bijective_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example {G : Type} [Group G] [Finite G]
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
      ∀ n, n ≠ 1 → Subsingleton (RelativeHomology ℤ (hg8_pair10 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) n) :=
  hg8_edgeRel_bijective U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **The triangle calculation.** For the lifted cells, the triangle classes form a basis of
`H₂(C, C¹; ℤ)`, and `H_n(C, C¹; ℤ) = 0` for `n ≠ 2`: by `hg8_skel_cells` and `hg8_tri_attach`,
`C ∖ C¹` is the disjoint union of the open lifted triangles, and excision with the
characteristic maps reduces the pair to copies of `(Δ², ∂Δ²)`, whose `H₂` is generated by the
identity simplex.
Source: Hatcher, *Algebraic Topology*, Lemma 2.34(a), Proposition 2.22 and Example 2.23;
Theorem 2.20 (excision). -/
theorem hg8_triRel_bijective {G : Type} [Group G] [Finite G]
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
      ∀ n, n ≠ 2 → Subsingleton (RelativeHomology ℤ (hg8_pair21 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) n) :=
  hg8_triRel_bijective_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example {G : Type} [Group G] [Finite G]
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
      ∀ n, n ≠ 2 → Subsingleton (RelativeHomology ℤ (hg8_pair21 (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) n) :=
  hg8_triRel_bijective U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **The connecting map of `(T¹, T⁰)` is `∂₁`.** For any `Δ`-map, the connecting map
`H₁(T¹, T⁰) → H₀(T⁰)` sends the class of the edge chain of `c` to the class of the vertex chain
of `hg2_bd1 ℤ g c`: the edge chain lifts its own relative class and its singular boundary is the
vertex chain (`hg5_bd_chain1`).
Source: Hatcher, *Algebraic Topology*, §2.1 (the boundary map of the long exact sequence of a
pair) and §2.2 (cellular boundary formula); Mathlib
`HomologicalComplex.HomologySequence.δ_apply`. -/
theorem hg8_connecting1 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (c : hg2_Edge G r →₀ ℤ) :
    hg8_delta (hg8_pair10 F) 0 (hg8_edgeRel F c) = hg8_vertClass F (hg2_bd1 ℤ g c) :=
  hg8_connecting1_aux F c

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (c : hg2_Edge G r →₀ ℤ) :
    hg8_delta (hg8_pair10 F) 0 (hg8_edgeRel F c) = hg8_vertClass F (hg2_bd1 ℤ g c) :=
  hg8_connecting1 F c

/-- **The connecting map of `(T, T¹)` is `∂₂`.** For any `Δ`-map, the connecting map
`H₂(T, T¹) → H₁(T¹)` followed by the projection `H₁(T¹) → H₁(T¹, T⁰)` sends the class of the
triangle chain of `w` to the class of the edge chain of `hg2_bd2 ℤ g w`: the singular boundary
of the triangle chain is the edge chain (`hg5_bd_chain2`), a cycle in `T¹`.
Source: Hatcher, *Algebraic Topology*, §2.2 (the cellular boundary `d₂` as the composite of
connecting map and projection); Mathlib `HomologicalComplex.HomologySequence.δ_apply`. -/
theorem hg8_connecting2 {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (w : hg2_Tri G r →₀ ℤ) :
    hg8_proj (hg8_pair10 F) 1 (hg8_delta (hg8_pair21 F) 1 (hg8_triRel F w)) =
      hg8_edgeRel F (hg2_bd2 ℤ g w) :=
  hg8_connecting2_aux F w

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (w : hg2_Tri G r →₀ ℤ) :
    hg8_proj (hg8_pair10 F) 1 (hg8_delta (hg8_pair21 F) 1 (hg8_triRel F w)) =
      hg8_edgeRel F (hg2_bd2 ℤ g w) :=
  hg8_connecting2 F w

/-- **The degree-one comparison is bijective.** For the lifted cells on the filling `C`, the map
`hg8_H1map : hg2_H1 ℤ g → b6m_H1 C` induced by the cellular-to-singular chain map is a
bijection. From the skeletal pairs: `H₁(C) ≅ H₁(C²) ≅ ker ∂₁ / im ∂₂` by the exact sequences of
`(C¹, C⁰)`, `(C, C¹)` and the triple, with the bases and connecting maps of
`hg8_vertClass_bijective`, `hg8_edgeRel_bijective`, `hg8_triRel_bijective`,
`hg8_connecting1`, `hg8_connecting2`; the isomorphism so obtained sends the class of a cellular
cycle to the class of its singular image, which is `hg8_H1map`.
Source: Hatcher, *Algebraic Topology*, Lemma 2.34 and Theorem 2.35 (cellular and singular
homology agree); Theorem 2.27 (simplicial and singular homology agree). -/
theorem hg8_H1map_bijective {G : Type} [Group G] [Finite G]
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
    Function.Bijective (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) :=
  hg8_H1map_bijective_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example {G : Type} [Group G] [Finite G]
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
    Function.Bijective (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) :=
  hg8_H1map_bijective U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **Deck equivariance of the comparison.** For the lifted cells, the comparison intertwines the
cellular deck action `hg2_H1act ℤ g h` with the singular map of `c ↦ h • c`: the deck
transformation `h` carries the lifted edge `ε` to the lifted edge `hg2_actEdge h ε`
(`hg5_lift_deck` on the `A`-triangles), so the chain map is equivariant.
Source: `hg5_lift_deck`; Hatcher, *Algebraic Topology*, §2.1 (naturality of induced maps). -/
theorem hg8_H1map_deck {G : Type} [Group G] [Finite G]
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
      homologyMap ℤ 1 (TopCat.ofHom ⟨fun c : C ↦ h • c, hC h⟩) (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) x) :=
  hg8_H1map_deck_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL h x

example {G : Type} [Group G] [Finite G]
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
      homologyMap ℤ 1 (TopCat.ofHom ⟨fun c : C ↦ h • c, hC h⟩) (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) x) :=
  hg8_H1map_deck U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL h x

/-! ## Checks -/

/-- The lifted `Δ`-map has the step-B cells: the triangles `L`, the edges `hg5_liftEdge L` and the
vertices `hg5_liftVert g L`. -/
example {G : Type} [Group G] [Finite G]
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
    (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL).tri = L ∧ (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL).edge = hg5_liftEdge L ∧
      (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL).vert = hg5_liftVert g L :=
  ⟨rfl, rfl, rfl⟩

/-- **Chain check toward stage H5 (`hg6_parameterLattice_transport`).** For `b4b_root`, at every
parameter `t` of every `V` in the polydisc about `mr_base`, the comparison transported to the
actual fibre `b63l_parameterFibre mr_base C V hV t` by the product coordinate is a deck-equivariant
linear equivalence `hg2_H1 ℤ b4b_root ≃ₗ[ℤ] b6m_H1 (fibre)` of exactly the shape that H5's
statement 3 quantifies over, so it carries the saturated cellular lattice `hg6_cellLattice` onto
`b63l_parameterLattice` and the cellular centre to `b63d_centre`. From `hg8_H1map_bijective`,
`hg8_H1map_deck` and `hg6_parameterLattice_transport`. -/
theorem hg8_parameterLattice_check (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction b4b_Group C]
    (hC : ∀ h : b4b_Group, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : b4b_Group) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri b4b_Group 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) :
    ∃ e : hg2_H1 ℤ b4b_root ≃ₗ[ℤ] b6m_H1 (b63l_parameterFibre mr_base C V hV t),
      (∀ x, e x = b6m_H1Equiv (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm
        (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) x)) ∧
      (∀ h x, e (hg2_H1act ℤ b4b_root h x) =
        homologyMap ℤ 1 (TopCat.ofHom (b6m_deck mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ h))
          (e x)) ∧
      hg6_cellLattice.map (e : hg2_H1 ℤ b4b_root →ₗ[ℤ] _) =
        b63l_parameterLattice mr_base C hC V hV t ∧
      ∀ x, e (hg6_cellCentre x) = b63d_centre mr_base C hC V hV t (e x) := by
  set F := (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)
  set s : b6t_polydisc mr_base := ⟨t.val, hV t.property⟩
  set k := b6m_coordinate mr_base C s
  let e : hg2_H1 ℤ b4b_root ≃ₗ[ℤ] b6m_H1 (b63l_parameterFibre mr_base C V hV t) :=
    (LinearEquiv.ofBijective (hg8_H1map F)
      (hg8_H1map_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)).trans (b6m_H1Equiv k.symm)
  have he : ∀ h x, e (hg2_H1act ℤ b4b_root h x) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck mr_base b4b_Group C hC s h)) (e x) := by
    intro h x
    have hd := hg8_H1map_deck U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL h x
    change b6m_H1Equiv k.symm (hg8_H1map F (hg2_H1act ℤ b4b_root h x)) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck mr_base b4b_Group C hC s h))
        (b6m_H1Equiv k.symm (hg8_H1map F x))
    rw [hd]
    have hsq : TopCat.ofHom (⟨fun c : C ↦ h • c, hC h⟩ : C(C, C)) ≫
        TopCat.ofHom (⟨k.symm, k.symm.continuous⟩ : C(C, b6m_Fibre mr_base C s)) =
        TopCat.ofHom (⟨k.symm, k.symm.continuous⟩ : C(C, b6m_Fibre mr_base C s)) ≫
          TopCat.ofHom (b6m_deck mr_base b4b_Group C hC s h) := by
      ext c; rfl
    have hcomp := congrArg (fun φ ↦ homologyMap ℤ 1 φ (hg8_H1map F x)) hsq
    simp only [homologyMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    exact hcomp
  obtain ⟨h1, h2⟩ := hg6_parameterLattice_transport mr_base C hC V hV t e he
  exact ⟨e, fun _ ↦ rfl, he, h1, h2⟩

/-- **Toward step D: the projector and the exact scaled image.** For `b4b_root`, the comparison
carries the cellular operator `hg2_projector = Σ_h b4b_projectorCoeff h · h_*` to the singular
operator `b63l_homologyOperator C hC`, and the exact image of the first (before any saturation)
onto the exact image of the second. From `hg8_H1map_deck` (termwise) and the surjectivity half
of `hg8_H1map_bijective`. -/
theorem hg8_projector_check (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction b4b_Group C]
    (hC : ∀ h : b4b_Group, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : b4b_Group) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c')
    (hstab : ∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j))
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri b4b_Group 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ x, hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) (hg2_projector x) =
      b63l_homologyOperator C hC (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL) x)) ∧
    (LinearMap.range hg2_projector).map (hg8_H1map (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)) =
      LinearMap.range (b63l_homologyOperator C hC) := by
  set F := (hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)
  have hcomm : ∀ x, hg8_H1map F (hg2_projector x) =
      b63l_homologyOperator C hC (hg8_H1map F x) := by
    intro x
    simp only [hg2_projector, b63l_homologyOperator, LinearMap.sum_apply,
      LinearMap.smul_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [hg8_H1map_deck U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL h x]
    rfl
  refine ⟨hcomm, ?_⟩
  have hsurj := (hg8_H1map_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL).2
  have hc : hg8_H1map F ∘ₗ hg2_projector = b63l_homologyOperator C hC ∘ₗ hg8_H1map F :=
    LinearMap.ext hcomm
  rw [← LinearMap.range_comp, hc, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj,
    Submodule.map_top]

/-- **Satisfiability of all binders, the family of lifts included.** At `mr_base` there exist, at
once, a base point over `b₀`, the explicit loop classes, a cover from `mr_rootCover` with every
cover binder of the lifted statements for `G = b4b_Group`, `g = b4b_root`, and a family of lifts
`L` with `hL`, taken from `hg5_lift_existsUnique` (with a body). -/
example : ∃ (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : π ⁻¹' {y₀})
    (C : Type) (_ : TopologicalSpace C) (_ : T2Space C) (_ : CompactSpace C)
    (_ : MulAction b4b_Group C) (f : C → OnePoint ℂ) (ι : U → C)
    (L : hg2_Tri b4b_Group 13 → C(StdSimplex ℝ (Fin 3), C)),
    (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ) ∧
    (∀ i, mr_IsLoop mr_base y₀ i (γ i)) ∧
    (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
    (∀ h : b4b_Group, Continuous (fun c : C ↦ h • c)) ∧ Continuous f ∧
    (∀ (h : b4b_Group) (c : C), f (h • c) = f c) ∧
    (∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c') ∧
    (∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j)) ∧
    Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ ∧
    (∀ u, f (ι u) = π u) ∧ (∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u) ∧
    (∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) := by
  have hb₀ : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    simpa [hg3_arc] using hg3_arc_mem_base 0 0
  let y₀ : b6t_punctured mr_base := ⟨_, hb₀⟩
  have hγ := fun i ↦
    (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose_spec
  set γ := fun i ↦ (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose
  obtain ⟨U, tU, aU, -, π, hπ, u₀, hroot, C, tC, cC, mC, t2C, compC, -, aC, -, f, ι, hf, hgal,
    -, hact, hι, hιr, hfι, hιG, -, hrot⟩ := mr_rootCover y₀ γ hγ
  have hL := fun τ ↦ (hg5_lift_existsUnique U π hπ y₀ rfl u₀ C f hf.continuous hgal.2 ι hι hιr hfι
    τ).exists.choose_spec
  refine ⟨y₀, γ, U, tU, aU, π, hπ, u₀, C, tC, t2C, compC, aC, f, ι, _, rfl, hγ, hroot,
    fun h ↦ (hact h).continuous, hf.continuous, hgal.1, hgal.2, fun j ↦ ?_, hι, hιr, hfι, hιG,
    hL⟩
  obtain ⟨c, hc, hr⟩ := hrot j
  exact ⟨c, hc, hr.2.1.symm⟩

/-- **The base decomposition is an instance of the generic statements.** Its vertices are
injective (`hg5_open_cells`, with a body), so `hg8_vertClass_bijective` applies to it with the
trivial group. -/
example : Function.Injective hg8_baseMap.vert := hg5_open_cells.2.2.2.2

example : Function.Bijective (hg8_vertClass hg8_baseMap) :=
  hg8_vertClass_bijective hg8_baseMap hg5_open_cells.2.2.2.2

/-- **The lifted vertices are injective** (`hg5_lift_vertices`, with a body), so
`hg8_vertClass_bijective` applies to the lifted `Δ`-map. -/
example {G : Type} [Group G] [Finite G]
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
    Function.Injective (hg8_liftMap U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL).vert :=
  (hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L
    hL).2

/-- **Non-degeneracy: `∂₁` is nonzero for `b4b_root`.** The edge `e_0(1)` runs from `b₀(1)` to
`p_0(⟨g_0⟩)`, two different vertices, so the connecting map of `hg8_connecting1` is not zero. -/
example : hg2_bd1 ℤ b4b_root (Finsupp.single (Sum.inl (0, 1)) 1) ≠ 0 := by
  intro h
  have h' := congrArg (fun z ↦ z (Sum.inl 1)) h
  simp [hg2_bd1, hg2_src, hg2_tgt] at h'

/-- **Non-degeneracy: `∂₂` is nonzero for `b4b_root`.** The boundary of `A_0(1)` has coefficient
`1` on its face `e_0(1)`, so the connecting map of `hg8_connecting2` is not zero. -/
example : hg2_bd2 ℤ b4b_root (Finsupp.single (Sum.inl (0, 1)) 1) ≠ 0 := by
  intro h
  have h' := congrArg (fun z ↦ z (Sum.inl (0, 1))) h
  simp [hg2_bd2, hg2_face0, hg2_face1, hg2_face2] at h'

/-- **No rank-zero case.** The source `hg2_H1 ℤ b4b_root` of the bijection `hg8_H1map_bijective`
contains the rank-`12` image of the B6-3b projector (`hg2_projector_basis`), so the comparison
is between nonzero groups; the base decomposition, a sphere, is not claimed to carry rank. -/
example : Nonempty (Module.Basis (Fin 12) ℤ (LinearMap.range hg2_projector)) :=
  hg2_projector_basis

end HodgeLean.Foundations.Program
