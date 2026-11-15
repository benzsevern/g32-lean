import HodgeLean.Foundations.Program.PrymParabolicProjectedProofs

/-! # H3b step D: exact projected images and their saturations

Each statement is an implication from the explicit marked-cover and lifted-simplex data.
The exact-image restrictions precede saturation; the saturated comparison respects the centre.
The last statement transports H5 coordinate evaluation to the rational lattice of each fibre.
The geometric cup/intersection comparison and the discriminant remain for H4 and H7.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular Convexity HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The restriction to the exact integral images, before saturation.
Source: `hg8_projector_check`; Hatcher, *Algebraic Topology*, Theorem 2.35. -/
theorem hg9_exact_comparison (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : LinearMap.range hg2_projector ≃ₗ[ℤ] LinearMap.range (b63l_homologyOperator C hC),
      ∀ x, (E x : b6m_H1 C) = hg8_H1map F x :=
  hg9_exact_comparison_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : LinearMap.range hg2_projector ≃ₗ[ℤ] LinearMap.range (b63l_homologyOperator C hC),
      ∀ x, (E x : b6m_H1 C) = hg8_H1map F x :=
  hg9_exact_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- The restriction to the saturations in ambient integral homology.
Source: Bourbaki, *Algebra*, Ch. VII, §1; `hg6_saturated_transport`. -/
theorem hg9_saturated_comparison (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_saturation (LinearMap.range (b63l_homologyOperator C hC)),
      ∀ x, (E x : b6m_H1 C) = hg8_H1map F x :=
  hg9_saturated_comparison_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_saturation (LinearMap.range (b63l_homologyOperator C hC)),
      ∀ x, (E x : b6m_H1 C) = hg8_H1map F x :=
  hg9_saturated_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- The exact-image comparison on every actual parameter fibre.
Source: `hg8_projector_check`, `b6m_coordinate`; Birkenhake–Lange, *Complex Abelian Varieties*, §12.2. -/
theorem hg9_fibre_exact_comparison (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : LinearMap.range hg2_projector ≃ₗ[ℤ]
        b63l_fibreScaledImage mr_base C hC ⟨t.val, hV t.property⟩,
      ∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x :=
  hg9_fibre_exact_comparison_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : LinearMap.range hg2_projector ≃ₗ[ℤ]
        b63l_fibreScaledImage mr_base C hC ⟨t.val, hV t.property⟩,
      ∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x :=
  hg9_fibre_exact_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

/-- The canonical forward map carries the saturated cellular lattice onto the parameter lattice.
Source: `hg8_parameterLattice_check`, `hg6_parameterLattice_transport`; Bourbaki, *Algebra*, Ch. VII, §1. -/
theorem hg9_parameterLattice_map (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    hg6_cellLattice.map (hg9_toFibre F V hV t) = b63l_parameterLattice mr_base C hC V hV t :=
  hg9_parameterLattice_map_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    hg6_cellLattice.map (hg9_toFibre F V hV t) = b63l_parameterLattice mr_base C hC V hV t :=
  hg9_parameterLattice_map U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

/-- The saturated comparison respects the centre and the integral expression for √−3.
Source: `hg6_parameterLattice_transport`, `hg6_cellCentreL`, `b63d_operator`; G32 v0.16, §3.3. -/
theorem hg9_centre_comparison (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t,
      (∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      (∀ x, (E (hg6_cellCentreL x) : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) =
        b63d_centre mr_base C hC V hV t (E x)) ∧
      ∀ x, (E (hg6_cellOperator x) : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) =
        b63d_operator mr_base C hC V hV t (E x) :=
  hg9_centre_comparison_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t,
      (∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      (∀ x, (E (hg6_cellCentreL x) : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) =
        b63d_centre mr_base C hC V hV t (E x)) ∧
      ∀ x, (E (hg6_cellOperator x) : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) =
        b63d_operator mr_base C hC V hV t (E x) :=
  hg9_centre_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

/-- A deck element fails to preserve both corresponding saturated coordinate summands.
Source: `hg6_lattice_not_deck_stable`, `hg8_H1map_deck`; G32 v0.16, Definition 3.2. -/
theorem hg9_not_deck_stable (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ (h : b4b_Group) (x : hg2_H1 ℤ b4b_root), x ∈ hg6_cellLattice ∧
      hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice ∧
      homologyMap ℤ 1 (TopCat.ofHom
        (b6m_deck mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ h))
        (hg9_toFibre F V hV t x) ∉ b63l_parameterLattice mr_base C hC V hV t :=
  hg9_not_deck_stable_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ (h : b4b_Group) (x : hg2_H1 ℤ b4b_root), x ∈ hg6_cellLattice ∧
      hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice ∧
      homologyMap ℤ 1 (TopCat.ofHom
        (b6m_deck mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ h))
        (hg9_toFibre F V hV t x) ∉ b63l_parameterLattice mr_base C hC V hV t :=
  hg9_not_deck_stable U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

/-- H5 coordinate evaluation on the rational lattice of an actual parameter fibre.
The image condition records the K-linear dual for the transported √−3 operator.
Source: `hg6_isotypic_comparison`; G32 v0.16, Proposition 6.1; Hatcher, §3.1, Theorem 3.2. -/
theorem hg9_isotypic_fibre_comparison (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t,
      (∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K]
          ((ℚ ⊗[ℤ] b63l_parameterLattice mr_base C hC V hV t) →ₗ[ℚ] hp_K),
        Function.Injective Θ ∧
        (∀ φ, φ ∈ LinearMap.range Θ ↔ ∀ x : ℚ ⊗[ℤ] hg6_cellLattice,
          φ (E.toLinearMap.baseChange ℚ (hg6_cellJ x)) =
            QuadraticAlgebra.omega * φ (E.toLinearMap.baseChange ℚ x)) ∧
        ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
          Θ (Submodule.Quotient.mk c)
            ((1 : ℚ) ⊗ₜ[ℤ] E ⟨Submodule.Quotient.mk z, hz⟩) = hg6_pairVec c.1 z.1 0 :=
  hg9_isotypic_fibre_comparison_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t,
      (∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K]
          ((ℚ ⊗[ℤ] b63l_parameterLattice mr_base C hC V hV t) →ₗ[ℚ] hp_K),
        Function.Injective Θ ∧
        (∀ φ, φ ∈ LinearMap.range Θ ↔ ∀ x : ℚ ⊗[ℤ] hg6_cellLattice,
          φ (E.toLinearMap.baseChange ℚ (hg6_cellJ x)) =
            QuadraticAlgebra.omega * φ (E.toLinearMap.baseChange ℚ x)) ∧
        ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
          Θ (Submodule.Quotient.mk c)
            ((1 : ℚ) ⊗ₜ[ℤ] E ⟨Submodule.Quotient.mk z, hz⟩) = hg6_pairVec c.1 z.1 0 :=
  hg9_isotypic_fibre_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t

/-- Joint satisfiability, constructed from the marked root cover and existing lifted cells.
The parameter domain is inhabited at `mr_base`.
Source: `mr_rootCover`, `hg5_lift_existsUnique`, `hg3_base_mem_polydisc`. -/
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
      L τ (StdSimplex.single 0) = hg5_triSheet τ • ι u₀) ∧
    ∃ (V : Set (Fin 10 → ℂ)) (_hV : V ⊆ b6t_polydisc mr_base) (t : V),
      t.val = mr_base := by
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
    hL, ?_⟩
  · obtain ⟨c, hc, hr⟩ := hrot j
    exact ⟨c, hc, hr.2.1.symm⟩
  · exact ⟨b6t_polydisc mr_base, fun _ hx ↦ hx, ⟨mr_base, hg3_base_mem_polydisc⟩, rfl⟩

/-- The exact source has positive rank.
Source: `hg2_projector_rank`. -/
example : Module.finrank ℤ (LinearMap.range hg2_projector) = 12 := hg2_projector_rank

/-- The saturated source has a nonempty index set of twelve basis vectors.
Source: `hg6_cellLattice_basis`. -/
example : Nonempty (Module.Basis (Fin 12) ℤ hg6_cellLattice) := hg6_cellLattice_basis

/-- The centre is nontrivial on the saturated source.
Source: `hg6_cellCentreL_ne_id`. -/
example : hg6_cellCentreL ≠ LinearMap.id := hg6_cellCentreL_ne_id

/-- Every local monodromy generator is nonidentity.
Source: `b63_root_order`. -/
example (i : Fin 13) : b4b_root i ≠ 1 := by
  intro h
  have ho := b63_root_order i
  rw [h, orderOf_one] at ho
  split_ifs at ho <;> norm_num at ho

/-- Chain check for the fibre K-structure: the actual operator squares to minus three
on the canonically identified saturated lattice.
Source: `hg9_centre_comparison`, `hg6_cellOperator_sq`; G32 v0.16, §3.3. -/
example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t,
      (∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      ∀ x, b63d_operator mr_base C hC V hV t
          (b63d_operator mr_base C hC V hV t (E x)) = (-3 : ℤ) • (E x).val := by
  obtain ⟨E, hE, _, hJ⟩ := hg9_centre_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t
  refine ⟨E, hE, fun x ↦ ?_⟩
  rw [← hJ x, ← hJ (hg6_cellOperator x), hg6_cellOperator_sq]
  exact congrArg Subtype.val (E.map_smul (-3 : ℤ) x)

/-- Chain check toward `g32d_ParabolicPolarization`: H5 evaluation on an actual fibre
and the cellular certificate Gram calculation are simultaneously available.
Identifying this cellular form with the geometric Weil Hermitian form is H4's remaining input.
Source: `hg9_isotypic_fibre_comparison`, `hg6_coordCup_gram`. -/
example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL;
    ∃ E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t,
      (∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K]
          ((ℚ ⊗[ℤ] b63l_parameterLattice mr_base C hC V hV t) →ₗ[ℚ] hp_K),
        Function.Injective Θ ∧
        (∀ φ, φ ∈ LinearMap.range Θ ↔ ∀ x : ℚ ⊗[ℤ] hg6_cellLattice,
          φ (E.toLinearMap.baseChange ℚ (hg6_cellJ x)) =
            QuadraticAlgebra.omega * φ (E.toLinearMap.baseChange ℚ x)) ∧
        ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
          Θ (Submodule.Quotient.mk c)
            ((1 : ℚ) ⊗ₜ[ℤ] E ⟨Submodule.Quotient.mk z, hz⟩) = hg6_pairVec c.1 z.1 0) ∧
    (∀ a b : Fin 6,
      (1 + 2 * pc_zeta) * (4 * hg6_coordCup b4b_root 0 0
        (hg_shapiroCochain hg4_sigmaK b4b_root (hp_certK a))
        (hg_shapiroCochain hg4_sigmaK b4b_root (hp_certK b))) =
      (Fintype.card b4b_Group : hp_K) * g32H0 pc_zeta a b) :=
  ⟨hg9_isotypic_fibre_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t, hg6_coordCup_gram⟩

end HodgeLean.Foundations.Program
