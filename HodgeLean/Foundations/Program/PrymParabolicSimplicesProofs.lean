import HodgeLean.Foundations.Program.PrymParabolicSimplicesLift

/-! # Proofs for stage H3b steps A and B: the base simplices and their lifts

The `_aux` theorems that `PrymParabolicSimplices.lean` restates.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex Convexity

namespace HodgeLean.Foundations.Program

theorem hg5_edge_ends_aux (ε : hg2_Edge Unit 13) :
    hg5_edge ε 0 = hg5_vert (hg2_src hg5_one ε) ∧ hg5_edge ε 1 = hg5_vert (hg2_tgt hg5_one ε) :=
  hg5_edge_ends_proof ε

theorem hg5_faces_aux (τ : hg2_Tri Unit 13) :
    hg5_face (hg5_tri τ) 0 = hg5_edge (hg2_face0 hg5_one τ) ∧
      hg5_face (hg5_tri τ) 1 = hg5_edge (hg2_face1 τ) ∧
      hg5_face (hg5_tri τ) 2 = hg5_edge (hg2_face2 τ) :=
  hg5_faces_proof τ

theorem hg5_edge_marks_aux (ε : hg2_Edge Unit 13) (s : unitInterval) :
    hg5_edge ε s ∈ Set.range (b6_branch mr_base) ↔
      (∃ i : Fin 13, ε = Sum.inl (i, ()) ∧ s = 1) ∨
        (∃ i : Fin 13, ε = Sum.inr (Sum.inr (i, ())) ∧ s = 0) :=
  hg5_edge_marks_proof ε s

theorem hg5_tri_injective_aux (τ : hg2_Tri Unit 13) : Function.Injective (hg5_tri τ) :=
  hg5_tri_injective_proof τ

theorem hg5_open_cells_aux :
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
  hg5_open_cells_proof

theorem hg5_cover_aux (z : OnePoint ℂ) :
    ∃ (τ : hg2_Tri Unit 13) (a : StdSimplex ℝ (Fin 3)), hg5_tri τ a = z :=
  hg5_cover_proof z

theorem hg5_lift_existsUnique_aux {G : Type} [Group G] [Finite G]
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
  hg5_lift_existsUnique_proof hπ hy₀ u₀ hf hftr hι hιr hfι τ

theorem hg5_lift_faces_aux {G : Type} [Group G]
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
      hg5_face (L τ) 2 = hg5_liftEdge L (hg2_face2 τ) := by
  have _ := hf
  exact hg5_lift_faces_proof hπ hy₀ u₀ g γ hγ hroot hι hιr hfι hιG L hL τ

theorem hg5_lift_vertices_aux {G : Type} [Group G] [Finite G]
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
      Function.Injective (hg5_liftVert g L) := by
  have _ := hf
  exact hg5_lift_vertices_proof hπ hy₀ u₀ g γ hγ hroot hC hfinv hftr hstab hι hιr hfι hιG L hL

theorem hg5_lift_cells_aux {G : Type} [Group G]
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
        (∀ k, 0 < a.weights k) → (∀ k, 0 < a'.weights k) → L τ a = L τ' a' → τ = τ' ∧ a = a' := by
  have _ := hy₀
  exact hg5_lift_cells_proof hπ hC hf hfinv hftr hι hιr hfι hιG (u₀ : U) L hL

end HodgeLean.Foundations.Program
