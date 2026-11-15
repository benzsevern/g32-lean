import HodgeLean.Foundations.Program.PrymParabolicSimplicesProofs

/-! # Stage H3b steps A and B: singular simplices of the base decomposition and their lifts (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h3s.md` (`docs/specs/PrymParabolicSimplices.md`).
Each theorem restates the matching `_aux` theorem in `PrymParabolicSimplicesProofs.lean`.

**Claimed (once the bodies are proved).**
- *Step A, at `mr_base`.* The explicit edges `e_i`, `f_i`, `h_i` and triangles `A_i`, `B_i` of
  G32 Figure 1 (`hg5_edge`, `hg5_tri`, indexed by the cells of H3a's complex for the trivial
  group) are singular simplices of the sphere whose endpoints are the vertices `b₀`, `b_∞`,
  `p_i` named by `hg2_src`, `hg2_tgt`, and whose faces are the edges named by
  `hg2_face0/1/2`; an edge meets the marks only at its endpoint `p_i`; each triangle is
  injective; the open triangles, the open edges and the vertices are pairwise disjoint; the
  triangles cover the sphere.
- *Step B, on a cover of the shape of `mr_rootCover`.* Each triangle lifts uniquely to the
  compact filling `C` from the point `x • ι u₀` over `b₀`; for any family of these lifts, the
  lifted faces follow `hg2_face0/1/2` for the tuple `g` of the marked monodromy, the endpoints
  of the lifted edges follow `hg2_src`, `hg2_tgt`, distinct vertices of `X̃(g)` lift to distinct
  points (the `p_i`-vertices exactly by the cosets of `⟨g_i⟩`), and the lifted triangles cover `C`
  with disjoint interiors.

Checks with bodies: the cellular-to-singular maps commute with the boundaries in degrees `2 → 1`
and `1 → 0`, at the base and for the lifts (derived from the statements); the orientation chain
`Σ (A_i − B_i)` of the base is a singular cycle; the lifts are permuted by the deck group as
`hg2_actTri`; the transport of the base cells to every configuration `t` of the polydisc.

Each statement is an implication from its binders. The cover binders are the conclusions of
`mr_rootCover` (witnessed with a body below at `mr_base`); the lift family `L` is witnessed by
`hg5_lift_existsUnique`.

**Not claimed.** Any homology equivalence: face-compatible simplices, even with disjoint
interiors and coverage, give no comparison of cellular and singular homology without the
excision and attachment arguments of step C. Lifts at configurations other than `mr_base`; the
lifted open edges as cells; the identification of the induced map on `H₁` with `b6m_H1`; the
projector comparison of step D. HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex Convexity

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## Step A: the base decomposition at `mr_base` -/

/-- **Endpoints of the base edges.** Each base edge runs from the vertex `hg2_src` to the vertex
`hg2_tgt` of H3a's complex for the trivial group: `e_i : b₀ → p_i`, `f_i : b₀ → b_∞`,
`h_i : p_i → b_∞`, with `p_12 = ∞` reached by the vertical rays.
Source: G32 v0.16, Figure 1; `hg3_arc`; the chart `w = 1 / (z + 11/2)` at `∞`. -/
theorem hg5_edge_ends (ε : hg2_Edge Unit 13) :
    hg5_edge ε 0 = hg5_vert (hg2_src hg5_one ε) ∧ hg5_edge ε 1 = hg5_vert (hg2_tgt hg5_one ε) :=
  hg5_edge_ends_aux ε

example (ε : hg2_Edge Unit 13) :
    hg5_edge ε 0 = hg5_vert (hg2_src hg5_one ε) ∧ hg5_edge ε 1 = hg5_vert (hg2_tgt hg5_one ε) :=
  hg5_edge_ends ε

/-- **Face compatibility.** The faces `0, 1, 2` of each base triangle (the restrictions to the
faces of the standard simplex opposite the vertices `0, 1, 2`) are the base edges named by
`hg2_face0`, `hg2_face1`, `hg2_face2`: `A_i` has faces `h_i, f_i, e_i` and `B_i` has faces
`h_i, f_{i+1}, e_i` (index mod `13`).
Source: G32 v0.16, Figure 1; barycentric computation on `hg5_wedge` and `hg5_coneFun`. -/
theorem hg5_faces (τ : hg2_Tri Unit 13) :
    hg5_face (hg5_tri τ) 0 = hg5_edge (hg2_face0 hg5_one τ) ∧
      hg5_face (hg5_tri τ) 1 = hg5_edge (hg2_face1 τ) ∧
      hg5_face (hg5_tri τ) 2 = hg5_edge (hg2_face2 τ) :=
  hg5_faces_aux τ

example (τ : hg2_Tri Unit 13) :
    hg5_face (hg5_tri τ) 0 = hg5_edge (hg2_face0 hg5_one τ) ∧
      hg5_face (hg5_tri τ) 1 = hg5_edge (hg2_face1 τ) ∧
      hg5_face (hg5_tri τ) 2 = hg5_edge (hg2_face2 τ) :=
  hg5_faces τ

/-- **The edges meet the marks only at `p_i`.** A point of a base edge is a mark exactly when it
is the end of an edge `e_i` or the start of an edge `h_i`; the arcs `f_i` avoid the marks
(`hg3_arc_avoids`).
Source: `mr_base`, `b6_branch`; elementary plane geometry (the edges `e_i`, `h_i` cross the real
axis only at `p_i`; the rays lie on the line `Re z = -11/2`). -/
theorem hg5_edge_marks (ε : hg2_Edge Unit 13) (s : unitInterval) :
    hg5_edge ε s ∈ Set.range (b6_branch mr_base) ↔
      (∃ i : Fin 13, ε = Sum.inl (i, ()) ∧ s = 1) ∨
        (∃ i : Fin 13, ε = Sum.inr (Sum.inr (i, ())) ∧ s = 0) :=
  hg5_edge_marks_aux ε s

example (ε : hg2_Edge Unit 13) (s : unitInterval) :
    hg5_edge ε s ∈ Set.range (b6_branch mr_base) ↔
      (∃ i : Fin 13, ε = Sum.inl (i, ()) ∧ s = 1) ∨
        (∃ i : Fin 13, ε = Sum.inr (Sum.inr (i, ())) ∧ s = 0) :=
  hg5_edge_marks ε s

/-- **Each triangle is injective.** For `i < 12` the weights `(a₀ − a₂, a₁)` are recovered from
the height `10 (a₀ − a₂)` and the real part, affine in `a₁` with slope `v − u ≠ 0`; for the cone
triangles the direction from `-11/2` recovers the arc parameter (the arc is star-shaped about
`-11/2`) and the distance recovers `a₀ + a₂`.
Source: barycentric coordinates; elementary plane geometry. -/
theorem hg5_tri_injective (τ : hg2_Tri Unit 13) : Function.Injective (hg5_tri τ) :=
  hg5_tri_injective_aux τ

example (τ : hg2_Tri Unit 13) : Function.Injective (hg5_tri τ) := hg5_tri_injective τ

/-- **Disjoint open cells.** Interior points of two base triangles coincide only in one triangle;
no interior point of a triangle lies on an edge; two interior points of edges coincide only on
one edge at one parameter; no interior point of an edge is a vertex; the vertices are distinct.
For `i < 12` the open triangle `A_i` (`B_i`) lies strictly between the profiles of `f_i` and of
`e_i ∪ h_i` (of `e_i ∪ h_i` and `f_{i+1}`) in sector `i`; `A_12`, `B_12` lie right and left of
the line `Re z = -11/2` outside the fan.
Source: `hg3_sector`, `hg3_profile`, `hg3_arc_interiors`; elementary plane geometry. -/
theorem hg5_open_cells :
    (∀ (τ τ' : hg2_Tri Unit 13) (a a' : StdSimplex ℝ (Fin 3)),
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) →
          hg5_tri τ a = hg5_tri τ' a' → τ = τ') ∧
      (∀ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), (∀ k, 0 < a.weights k) →
        ∀ (ε : hg2_Edge Unit 13) (s : unitInterval), hg5_tri τ a ≠ hg5_edge ε s) ∧
      (∀ (ε ε' : hg2_Edge Unit 13) (s s' : unitInterval), s ∈ Set.Ioo 0 1 →
        s' ∈ Set.Ioo 0 1 → hg5_edge ε s = hg5_edge ε' s' → ε = ε' ∧ s = s') ∧
      (∀ (ε : hg2_Edge Unit 13) (s : unitInterval), s ∈ Set.Ioo 0 1 →
        ∀ v, hg5_edge ε s ≠ hg5_vert v) ∧
      Function.Injective hg5_vert :=
  hg5_open_cells_aux

example :
    (∀ (τ τ' : hg2_Tri Unit 13) (a a' : StdSimplex ℝ (Fin 3)),
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) →
          hg5_tri τ a = hg5_tri τ' a' → τ = τ') ∧
      (∀ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), (∀ k, 0 < a.weights k) →
        ∀ (ε : hg2_Edge Unit 13) (s : unitInterval), hg5_tri τ a ≠ hg5_edge ε s) ∧
      (∀ (ε ε' : hg2_Edge Unit 13) (s s' : unitInterval), s ∈ Set.Ioo 0 1 →
        s' ∈ Set.Ioo 0 1 → hg5_edge ε s = hg5_edge ε' s' → ε = ε' ∧ s = s') ∧
      (∀ (ε : hg2_Edge Unit 13) (s : unitInterval), s ∈ Set.Ioo 0 1 →
        ∀ v, hg5_edge ε s ≠ hg5_vert v) ∧
      Function.Injective hg5_vert :=
  hg5_open_cells

/-- **Coverage.** Every point of the sphere lies on a base triangle: the triangles `A_i`, `B_i`
with their boundaries fill the closure of sector `i` (`hg3_sector_partition`).
Source: `hg3_sector_partition`, `hg3_fan`; elementary plane geometry. -/
theorem hg5_cover (z : OnePoint ℂ) :
    ∃ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), hg5_tri τ a = z :=
  hg5_cover_aux z

example (z : OnePoint ℂ) : ∃ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), hg5_tri τ a = z :=
  hg5_cover z

/-! ## Step B: the lifted cells -/

/-- **Unique lifts of the triangles.** On a quotient covering `π` of the punctured sphere at
`mr_base` with finite deck group `G`, openly embedded by `ι` in a compact Hausdorff filling
`f : C → S²` whose fibres are orbits, each base triangle lifts uniquely to `C` from the point
`x • ι u₀` over `b₀`. Away from its vertex `p_i` the triangle lies in the punctured sphere and
lifts through `π` (a simply connected domain); at `p_i` the lift extends continuously since the
fibre over `p_i` is finite and `f` is proper (`C` is compact); uniqueness on the connected complement of the
vertex and by the Hausdorff property at it.
Source: Hatcher, *Algebraic Topology*, Proposition 1.33 and 1.34; Forster, GTM 81, Theorem 4.23
(local normal form of a branched cover); `mr_rootCover`. -/
theorem hg5_lift_existsUnique {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u)
    (τ : hg2_Tri G 13) :
    ∃! σ : C(StdSimplex ℝ (Fin 3), C), (∀ a, f (σ a) = hg5_tri (hg5_triBase τ) a) ∧
      σ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀ :=
  hg5_lift_existsUnique_aux U π hπ y₀ hy₀ u₀ C f hf hftr ι hι hιr hfι τ

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction b4b_Group C]
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c')
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (τ : hg2_Tri b4b_Group 13) :
    ∃! σ : C(StdSimplex ℝ (Fin 3), C), (∀ a, f (σ a) = hg5_tri (hg5_triBase τ) a) ∧
      σ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀ :=
  hg5_lift_existsUnique U π hπ y₀ hy₀ u₀ C f hf hftr ι hι hιr hfι τ

/-- **Lifted faces follow `hg2_face0/1/2`.** For a cover whose marked monodromy sends the explicit
loop `γ i` to `op (g i)`, and any family `L` of lifts of the triangles (`L (A_i(x))` and
`L (B_i(x))` start at `x • ι u₀`), the faces of `L τ` are the lifted edges of H3a's labels: the
`f_{i+1}`- and `e_i`-faces of `L (B_i(x))` are those of `L (A_{i+1}(x))` and `L (A_i(x))` (lifts
of one path from one point), and its `h_i`-face is that of `L (A_i(x g_i⁻¹))`: both `h`-faces
end where the lifts of `f_{i+1}` from `x` and of `f_i` from `x g_i⁻¹` end, which agree by the
endpoint monodromy `hg3_ell_endpoint`.
Source: `hg3_ell_endpoint`, `hg3_arc_endpoint`; Hatcher, Proposition 1.30 and 1.34;
G32 v0.16, Figure 1. -/
theorem hg5_lift_faces {G : Type} [Group G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction G C]
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (τ : hg2_Tri G 13) :
    hg5_face (L τ) 0 = hg5_liftEdge L (hg2_face0 g τ) ∧
      hg5_face (L τ) 1 = hg5_liftEdge L (hg2_face1 τ) ∧
      hg5_face (L τ) 2 = hg5_liftEdge L (hg2_face2 τ) :=
  hg5_lift_faces_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C f hf ι hι hιr hfι hιG L hL τ

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction b4b_Group C]
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri b4b_Group 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (τ : hg2_Tri b4b_Group 13) :
    hg5_face (L τ) 0 = hg5_liftEdge L (hg2_face0 b4b_root τ) ∧
      hg5_face (L τ) 1 = hg5_liftEdge L (hg2_face1 τ) ∧
      hg5_face (L τ) 2 = hg5_liftEdge L (hg2_face2 τ) :=
  hg5_lift_faces U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C f hf ι hι hιr hfι hιG L hL τ

/-- **Lifted vertices.** Under the binders of `hg5_lift_faces`, for a finite deck group acting
continuously with fibres of `f` the orbits, and a point over each mark `p_j` whose stabilizer
has order `orderOf (g j)`: the lifted edges run between the lifted vertices named by `hg2_src`,
`hg2_tgt` (the `b_∞`-labels are those of `hg3_arc_endpoint`; the `p_i`-label does not depend on
the representative of the coset), and distinct vertices of `X̃(g)` lift to distinct points of
`C`. In particular the vertex `1` of `L (A_i(x))` and of `L (A_i(y))` agree exactly when
`x⟨g_i⟩ = y⟨g_i⟩`: its stabilizer contains `x g_i x⁻¹`, and has order `orderOf (g i)`.
Source: `hg3_arc_endpoint`; Forster, GTM 81, Theorem 4.23 and §5; Hatcher, Proposition 1.33. -/
theorem hg5_lift_vertices {G : Type} [Group G] [Finite G]
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
    (∀ ε : hg2_Edge G 13, hg5_liftEdge L ε 0 = hg5_liftVert g L (hg2_src g ε) ∧
        hg5_liftEdge L ε 1 = hg5_liftVert g L (hg2_tgt g ε)) ∧
      Function.Injective (hg5_liftVert g L) :=
  hg5_lift_vertices_aux U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι
    hιG L hL

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction b4b_Group C]
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
    (∀ ε : hg2_Edge b4b_Group 13, hg5_liftEdge L ε 0 = hg5_liftVert b4b_root L (hg2_src b4b_root ε) ∧
        hg5_liftEdge L ε 1 = hg5_liftVert b4b_root L (hg2_tgt b4b_root ε)) ∧
      Function.Injective (hg5_liftVert b4b_root L) :=
  hg5_lift_vertices U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
    hfι hιG L hL

/-- **The lifted triangles decompose the filling.** Under the cover binders, any family of lifts
covers `C` (a point of `C` lies over a point of some base triangle, and the deck group, acting
transitively on fibres, carries a lift through it to one of the family), and two interior points
of lifted triangles coincide only in one lifted triangle at one point (their images coincide in
one base triangle by `hg5_open_cells`, `hg5_tri_injective`; two lifts of one triangle agreeing at
a point agree everywhere, and the sheets of their `b₀`-vertices are then equal by freeness).
Source: Hatcher, Proposition 1.34 (unique lifting); `hg5_open_cells`, `hg5_tri_injective`,
`hg5_cover`. -/
theorem hg5_lift_cells {G : Type} [Group G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ c : C, ∃ (τ : hg2_Tri G 13) (a : StdSimplex ℝ (Fin 3)), L τ a = c) ∧
      ∀ (τ τ' : hg2_Tri G 13) (a a' : StdSimplex ℝ (Fin 3)),
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) → L τ a = L τ' a' → τ = τ' ∧ a = a' :=
  hg5_lift_cells_aux U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι hιG L hL

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction b4b_Group C]
    (hC : ∀ h : b4b_Group, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : b4b_Group) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c')
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri b4b_Group 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) :
    (∀ c : C, ∃ (τ : hg2_Tri b4b_Group 13) (a : StdSimplex ℝ (Fin 3)), L τ a = c) ∧
      ∀ (τ τ' : hg2_Tri b4b_Group 13) (a a' : StdSimplex ℝ (Fin 3)),
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) → L τ a = L τ' a' → τ = τ' ∧ a = a' :=
  hg5_lift_cells U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr ι hι hιr hfι hιG L hL

/-! ## Chain checks: cellular to singular chains -/

/-- **Degree `2 → 1`, for any family.** If the faces of a family of singular `2`-simplices are
the paths named by `d₀, d₁, d₂`, then the singular boundary of the image of a cellular
`2`-chain is the image of `d₀ − d₁ + d₂` of it. -/
theorem hg5_bd_chain2 {ι₂ ι₁ T : Type} [TopologicalSpace T]
    (σ : ι₂ → C(StdSimplex ℝ (Fin 3), T)) (e : ι₁ → C(unitInterval, T))
    (d₀ d₁ d₂ : ι₂ → ι₁)
    (h : ∀ τ, hg5_face (σ τ) 0 = e (d₀ τ) ∧ hg5_face (σ τ) 1 = e (d₁ τ) ∧
      hg5_face (σ τ) 2 = e (d₂ τ)) (c : ι₂ →₀ ℤ) :
    AlgebraicTopology.Simplicial.boundary ℤ 1 (hg5_chain2 σ c) =
      hg5_chain1 e (Finsupp.lmapDomain ℤ ℤ d₀ c - Finsupp.lmapDomain ℤ ℤ d₁ c +
        Finsupp.lmapDomain ℤ ℤ d₂ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]; simp only [map_add, map_sub]; abel
  | single τ n =>
    obtain ⟨h0, h1, h2⟩ := h τ
    simp only [hg5_chain2, hg5_chain1, Finsupp.linearCombination_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_add, map_sub]
    erw [LinearMap.map_smul, AlgebraicTopology.Simplicial.boundary_chainOfSimplex]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      hg5_delta_face, h0, h1, h2, Fin.val_zero, Fin.val_succ, pow_zero, add_zero]
    have p1 : ((-1 : ℤ)) ^ (0 + 1) = -1 := by norm_num
    have p2 : ((-1 : ℤ)) ^ (0 + 1 + 1) = 1 := by norm_num
    rw [p1, p2]
    erw [one_smul, one_smul, neg_smul, one_smul]
    rw [smul_add, smul_add, smul_neg]
    generalize n • AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e (d₀ τ))) = A
    generalize n • AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e (d₁ τ))) = B
    generalize n • AlgebraicTopology.Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e (d₂ τ))) = D
    abel

/-- **Degree `1 → 0`, for any family.** If the paths of a family start at the points named by
`s` and end at the points named by `t`, the singular boundary of the image of a cellular
`1`-chain is the image of `t − s` of it. -/
theorem hg5_bd_chain1 {ι₁ ι₀ T : Type} [TopologicalSpace T]
    (e : ι₁ → C(unitInterval, T)) (v : ι₀ → T) (s t : ι₁ → ι₀)
    (h : ∀ ε, e ε 0 = v (s ε) ∧ e ε 1 = v (t ε)) (c : ι₁ →₀ ℤ) :
    AlgebraicTopology.Simplicial.boundary ℤ 0 (hg5_chain1 e c) =
      hg5_chain0 v (Finsupp.lmapDomain ℤ ℤ t c - Finsupp.lmapDomain ℤ ℤ s c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]; simp only [map_add, map_sub]; abel
  | single ε n =>
    obtain ⟨h0, h1⟩ := h ε
    simp only [hg5_chain1, hg5_chain0, Finsupp.linearCombination_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_sub]
    erw [LinearMap.map_smul, AlgebraicTopology.Simplicial.boundary_chainOfSimplex]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      hg5_delta_path_zero, hg5_delta_path_one, ← h0, ← h1, Fin.val_zero, Fin.val_succ, pow_zero,
      add_zero]
    have p1 : ((-1 : ℤ)) ^ (0 + 1) = -1 := by norm_num
    rw [p1]
    erw [one_smul, neg_smul, one_smul]
    rw [smul_add, smul_neg]
    generalize n • AlgebraicTopology.Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (e ε 1)) = A
    generalize n • AlgebraicTopology.Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (e ε 0)) = B
    abel

/-- **Chain check (base, degree `2 → 1`).** The singular boundary of the image of a cellular
`2`-chain of the base decomposition is the image of its cellular boundary `hg2_bd2`. From
`hg5_faces`. -/
theorem hg5_base_chain2 (c : hg2_Tri Unit 13 →₀ ℤ) :
    AlgebraicTopology.Simplicial.boundary ℤ 1 (hg5_chain2 hg5_tri c) =
      hg5_chain1 hg5_edge (hg2_bd2 ℤ hg5_one c) := by
  rw [hg5_bd_chain2 hg5_tri hg5_edge _ _ _ hg5_faces c]
  rfl

/-- **Chain check (base, degree `1 → 0`).** From `hg5_edge_ends`. -/
theorem hg5_base_chain1 (c : hg2_Edge Unit 13 →₀ ℤ) :
    AlgebraicTopology.Simplicial.boundary ℤ 0 (hg5_chain1 hg5_edge c) =
      hg5_chain0 hg5_vert (hg2_bd1 ℤ hg5_one c) := by
  rw [hg5_bd_chain1 hg5_edge hg5_vert _ _ hg5_edge_ends c]
  rfl

/-- **The orientation chain of the base is a singular cycle.** The image of `Σ_i (A_i − B_i)`
(`hg2_orient` for the trivial group) has singular boundary zero: by `hg5_base_chain2` and
`hg2_cycles2` (the orientation chain is a cellular cycle for the trivial tuple, which has
product one and generates the trivial group). -/
theorem hg5_orient_cycle :
    AlgebraicTopology.Simplicial.boundary ℤ 1 (hg5_chain2 hg5_tri (hg2_orient (G := Unit))) = 0 := by
  rw [hg5_base_chain2]
  have hk : hg2_orient (G := Unit) (r := 13) ∈ LinearMap.ker (hg2_bd2 ℤ hg5_one) := by
    rw [hg2_cycles2 hg5_one rfl (Subsingleton.elim _ _)]
    exact Submodule.subset_span rfl
  rw [LinearMap.mem_ker.mp hk, map_zero]

/-- **Chain check (lifts, degree `2 → 1`).** For a family of lifts as in `hg5_lift_faces`, the
singular boundary of the image of a cellular `2`-chain of `X̃(g)` is the image of its cellular
boundary `hg2_bd2 ℤ g` under the lifted edges. From `hg5_lift_faces`. -/
theorem hg5_lift_chain2 {G : Type} [Group G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀}) (g : Fin 13 → G)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (C : Type) [TopologicalSpace C] [T2Space C] [MulAction G C]
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u) (hιG : ∀ (h : G) (u : U), ι (h • u) = h • ι u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (c : hg2_Tri G 13 →₀ ℤ) :
    AlgebraicTopology.Simplicial.boundary ℤ 1 (hg5_chain2 L c) =
      hg5_chain1 (hg5_liftEdge L) (hg2_bd2 ℤ g c) := by
  rw [hg5_bd_chain2 L (hg5_liftEdge L) _ _ _
    (hg5_lift_faces U π hπ y₀ hy₀ u₀ g γ hγ hroot C f hf ι hι hιr hfι hιG L hL) c]
  rfl

/-- **Chain check (lifts, degree `1 → 0`).** For a family of lifts as in `hg5_lift_vertices`,
the singular boundary of the image of a cellular `1`-chain of `X̃(g)` is the image of its
cellular boundary `hg2_bd1 ℤ g` under the lifted vertices. With `hg5_lift_chain2`, the lifted
cells give a chain map from the cellular chains of `X̃(g)` to the singular chains of `C` in
degrees `0–2`, the map toward `hg2_H1 ℤ b4b_root →ₗ[ℤ] b6m_H1 C` of step C. From
`hg5_lift_vertices`. -/
theorem hg5_lift_chain1 {G : Type} [Group G] [Finite G]
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
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (c : hg2_Edge G 13 →₀ ℤ) :
    AlgebraicTopology.Simplicial.boundary ℤ 0 (hg5_chain1 (hg5_liftEdge L) c) =
      hg5_chain0 (hg5_liftVert g L) (hg2_bd1 ℤ g c) := by
  rw [hg5_bd_chain1 (hg5_liftEdge L) (hg5_liftVert g L) _ _
    (hg5_lift_vertices U π hπ y₀ hy₀ u₀ g γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι
      hιG L hL).1 c]
  rfl

/-- **Deck equivariance of the lifts.** Under the binders of `hg5_lift_existsUnique`, with the
deck group acting continuously, `f` invariant and `ι` equivariant, any family of lifts satisfies
`h • L τ = L (hg2_actTri h τ)`: both lift the same base triangle from `(h x) • ι u₀`. From the
uniqueness half of `hg5_lift_existsUnique`. -/
theorem hg5_lift_deck {G : Type} [Group G] [Finite G]
    (U : Type) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (y₀ : b6t_punctured mr_base) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (u₀ : π ⁻¹' {y₀})
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [MulAction G C]
    (hC : ∀ h : G, Continuous (fun c : C ↦ h • c))
    (f : C → OnePoint ℂ) (hf : Continuous f)
    (hfinv : ∀ (h : G) (c : C), f (h • c) = f c)
    (hftr : ∀ c c' : C, f c = f c' → ∃ h : G, h • c = c')
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u)
    (L : hg2_Tri G 13 → C(StdSimplex ℝ (Fin 3), C))
    (hL : ∀ τ, (∀ a, f (L τ a) = hg5_tri (hg5_triBase τ) a) ∧
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀)
    (h : G) (τ : hg2_Tri G 13) (a : StdSimplex ℝ (Fin 3)) :
    h • L τ a = L (hg2_actTri h τ) a := by
  have hb : hg5_triBase (hg2_actTri h τ) = hg5_triBase τ := by
    rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl
  have hs : hg5_triSheet (hg2_actTri h τ) = h * hg5_triSheet τ := by
    rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl
  let σ' : C(StdSimplex ℝ (Fin 3), C) := ⟨fun b ↦ h • L τ b, (hC h).comp (L τ).continuous⟩
  have hσ' : (∀ b, f (σ' b) = hg5_tri (hg5_triBase (hg2_actTri h τ)) b) ∧
      σ' (StdSimplex.single 0) = hg5_triSheet (hg2_actTri h τ) • ι u₀ := by
    refine ⟨fun b ↦ ?_, ?_⟩
    · change f (h • L τ b) = _
      rw [hfinv, (hL τ).1 b, hb]
    · change h • L τ (StdSimplex.single 0) = _
      rw [(hL τ).2, hs, mul_smul]
  have huniq := (hg5_lift_existsUnique U π hπ y₀ hy₀ u₀ C f hf hftr ι hι hιr hfι
    (hg2_actTri h τ)).unique hσ' (hL _)
  exact DFunLike.congr_fun huniq a

/-! ## Transport to the polydisc -/

/-- **Transport: the pushed arcs are the arcs.** At every configuration `t` of the polydisc the
B6-2a push fixes each arc `f_i` pointwise (`hg3_arc_avoids`, `b6t_fixed`), so the transported
`f`-edges are the same singular simplices. -/
theorem hg5_push_edgeF (t : b6t_polydisc mr_base) (i : Fin 13) :
    (hg5_push t).comp (hg5_edgeF i) = hg5_edgeF i := by
  ext s
  exact (b6t_fixed mr_base mr_base_mem_chart t.val t.property).2.2.2 _
    (hg3_arc_avoids t.val t.property i s).2

/-- **Transport: faces.** The pushed triangles have the pushed edges as faces (`hg5_faces` and
naturality of restriction to faces). -/
theorem hg5_push_faces (t : b6t_polydisc mr_base) (τ : hg2_Tri Unit 13) :
    hg5_face ((hg5_push t).comp (hg5_tri τ)) 0 = (hg5_push t).comp (hg5_edge (hg2_face0 hg5_one τ)) ∧
      hg5_face ((hg5_push t).comp (hg5_tri τ)) 1 = (hg5_push t).comp (hg5_edge (hg2_face1 τ)) ∧
      hg5_face ((hg5_push t).comp (hg5_tri τ)) 2 = (hg5_push t).comp (hg5_edge (hg2_face2 τ)) := by
  obtain ⟨h0, h1, h2⟩ := hg5_faces τ
  exact ⟨by rw [← h0]; rfl, by rw [← h1]; rfl, by rw [← h2]; rfl⟩

/-- **Transport: marks.** At every configuration `t` of the polydisc, a point of a pushed edge is
a mark of `t` exactly when the point of the base edge is a mark of `mr_base`: the push is a
bijection of the sphere carrying the marks of `mr_base` to those of `t` (`b6t_homeomorph`,
`b6t_marks`). With `hg5_edge_marks`, the pushed `e_i` and `h_i` meet the marks of `t` only at
the moved mark `p_i`. -/
theorem hg5_push_marks (t : b6t_polydisc mr_base) (ε : hg2_Edge Unit 13) (s : unitInterval) :
    hg5_push t (hg5_edge ε s) ∈ Set.range (b6_branch t.val) ↔
      (∃ i : Fin 13, ε = Sum.inl (i, ()) ∧ s = 1) ∨
        (∃ i : Fin 13, ε = Sum.inr (Sum.inr (i, ())) ∧ s = 0) := by
  rw [← hg5_edge_marks ε s]
  obtain ⟨e, he⟩ := b6t_homeomorph mr_base mr_base_mem_chart t.val t.property
  have hm := b6t_marks mr_base mr_base_mem_chart t.val t.property
  change b6t_sphere mr_base t.val (hg5_edge ε s) ∈ _ ↔ _
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, e.injective ?_⟩
    rw [he, he, hm j, hj]
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [← hj, hm j]⟩

/-! ## Satisfiability and non-degeneracy -/

/-- **Satisfiability of the cover binders.** At `mr_base` there exist, at once, a base point
over `b₀`, the explicit loop classes, and a cover with every binder of `hg5_lift_existsUnique`,
`hg5_lift_faces`, `hg5_lift_vertices` and `hg5_lift_cells` for `G = b4b_Group`, `g = b4b_root`
(from `mr_rootCover` and `mr_loop_existsUnique`, both with bodies on `main`). The remaining
binder, the family `L` of lifts, is supplied by `hg5_lift_existsUnique`. -/
example : ∃ (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : π ⁻¹' {y₀})
    (C : Type) (_ : TopologicalSpace C) (_ : T2Space C) (_ : CompactSpace C)
    (_ : MulAction b4b_Group C) (f : C → OnePoint ℂ) (ι : U → C),
    (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ) ∧
    (∀ i, mr_IsLoop mr_base y₀ i (γ i)) ∧
    (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
    (∀ h : b4b_Group, Continuous (fun c : C ↦ h • c)) ∧ Continuous f ∧
    (∀ (h : b4b_Group) (c : C), f (h • c) = f c) ∧
    (∀ c c' : C, f c = f c' → ∃ h : b4b_Group, h • c = c') ∧
    (∀ j, ∃ c : C, f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j)) ∧
    Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ ∧
    (∀ u, f (ι u) = π u) ∧ (∀ (h : b4b_Group) (u : U), ι (h • u) = h • ι u) := by
  have hb₀ : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    simpa [hg3_arc] using hg3_arc_mem_base 0 0
  let y₀ : b6t_punctured mr_base := ⟨_, hb₀⟩
  have hγ := fun i ↦
    (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose_spec
  set γ := fun i ↦ (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose
  obtain ⟨U, tU, aU, -, π, hπ, u₀, hroot, C, tC, cC, mC, t2C, compC, -, aC, -, f, ι, hf, hgal,
    -, hact, hι, hιr, hfι, hιG, -, hrot⟩ := mr_rootCover y₀ γ hγ
  refine ⟨y₀, γ, U, tU, aU, π, hπ, u₀, C, tC, t2C, compC, aC, f, ι, rfl, hγ, hroot,
    fun h ↦ (hact h).continuous, hf.continuous, hgal.1, hgal.2, fun j ↦ ?_, hι, hιr, hfι, hιG⟩
  obtain ⟨c, hc, hr⟩ := hrot j
  exact ⟨c, hc, hr.2.1.symm⟩

/-- **Non-degeneracy of the base triangles.** The three vertices of `A_0` are distinct points
(`b₀`, the mark `-12`, `b_∞`), so the base simplices are not constant. -/
example : hg5_triA 0 (StdSimplex.single 0) ≠ hg5_triA 0 (StdSimplex.single 1) ∧
    hg5_triA 0 (StdSimplex.single 1) ≠ hg5_triA 0 (StdSimplex.single 2) ∧
    hg5_triA 0 (StdSimplex.single 0) ≠ hg5_triA 0 (StdSimplex.single 2) := by
  unfold hg5_triA
  simp only [show (0 : Fin 13).val < 12 by decide, ↓reduceDIte]
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro h
    have := congrArg Complex.im (OnePoint.coe_injective h)
    norm_num [hg5_wedge] at this

/-- **Non-degeneracy of the lifted monodromy (no trivial case).** For `g = b4b_root` the `h`-face
of `B_i(x)` is never the `h`-face of `A_i(x)`: the lifted triangles `A_i(x)` and `B_i(x)` are
glued along `h` with the shift `x ↦ x g_i⁻¹`, which is nontrivial since every `b4b_root i` has
order `2` or `3` (`b63_root_order`). -/
example (i : Fin 13) (x : b4b_Group) :
    hg2_face0 b4b_root (Sum.inr (i, x)) ≠ hg2_face0 b4b_root (Sum.inl (i, x)) := by
  intro h
  simp only [hg2_face0, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
  have h1 : b4b_root i = 1 := by
    have := mul_left_cancel (a := x) (h.trans (mul_one x).symm)
    exact inv_eq_one.mp this
  have h2 := b63_root_order i
  rw [h1, orderOf_one] at h2
  split_ifs at h2 <;> omega

/-- **The source of the lifted chain map has positive rank (no rank-zero case).** For
`g = b4b_root`, the cellular `H₁` that the lifted chain map carries toward `b6m_H1 C` contains
the rank-`12` image of the B6-3b projector (`hg2_projector_basis`). The base decomposition, a
triangulated sphere, has cellular `H₁` of rank `0`; the lift is what carries the rank. -/
example : Nonempty (Module.Basis (Fin 12) ℤ (LinearMap.range hg2_projector)) :=
  hg2_projector_basis

end HodgeLean.Foundations.Program
