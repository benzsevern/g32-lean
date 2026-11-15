import HodgeLean.Foundations.Program.PrymParabolicIntersectionProofs
import HodgeLean.Foundations.Program.PrymFamilyMarked

/-! # Stage H4, geometric part, first stage: the cellular cup form against the intersection form

Each statement is an implication from the marked root-cover data, the lifted simplices of step B
and, on a parameter fibre, a complex structure making the projection holomorphic together with
the B3 intersection form and the period comparison. Claimed: the chain-level Alexander–Whitney
comparison on the orientation chain; that the orientation cycle generates `H₂` of the filling;
that it is minus the complex fundamental class (local degree `−1`); that the singular and the
cellular cup products evaluated on it are minus the intersection form of the Poincaré duals; and
that on the saturated coordinate lattice the cup form on `H¹_σ` is a nonzero rational multiple of
the geometric Weil–Hermitian form, with the order of arguments fixed. Not claimed: the value of
that rational scale, the discriminant of the geometric form, the B5 normalization or `hpol`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity HodgeLean.Foundations
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- **Alexander–Whitney comparison on the orientation chain.** For every `Δ`-map of `X̃(g)` and
all singular `1`-cochains `φ, ψ`, the singular cup product `φ ∪ ψ` evaluated on the image of
`hg2_orient` is the cellular evaluation `hga_cupEval` of the restrictions of `φ, ψ` to the edges:
the front face `[v₀, v₁]` of each singular triangle is its edge `face₂` and the back face
`[v₁, v₂]` is its edge `face₀` (`F.faces`).
Source: Hatcher, *Algebraic Topology*, §3.2 (the cup product formula); `cupCochain_apply_simplex`,
`hg5_delta_face`. -/
theorem hga_aw_cellular {G : Type} [Group G] [Fintype G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1) :
    Singular.cupCochain (TopCat.of T) 1 1 φ ψ (hg5_chain2 F.tri hg2_orient) =
      hga_cupEval ℤ g (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1)))
        (fun ε ↦ ψ (hg5_chain1 F.edge (Finsupp.single ε 1))) :=
  hga_aw_cellular_aux F φ ψ

example {G : Type} [Group G] [Fintype G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1) :
    Singular.cupCochain (TopCat.of T) 1 1 φ ψ (hg5_chain2 F.tri hg2_orient) =
      hga_cupEval ℤ g (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1)))
        (fun ε ↦ ψ (hg5_chain1 F.edge (Finsupp.single ε 1))) :=
  hga_aw_cellular F φ ψ

/-- **The orientation cycle generates `H₂` of the filling.** For the lifted cells of the marked
root cover, `H₂(C; ℤ) ≅ ℤ` with the class of `Σ_τ hg2_orient(τ) [L τ]` going to `1`.
Source: Hatcher, *Algebraic Topology*, §3.3, Theorem 3.26 (compact connected orientable surfaces without boundary);
`hg2_cycles2`, `hg5_lift_cells`. -/
theorem hga_fundClass_generator (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    ∃ e : Homology ℤ (TopCat.of C) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1 :=
  hga_fundClass_generator_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

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
    ∃ e : Homology ℤ (TopCat.of C) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1 :=
  hga_fundClass_generator U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL

/-- **The sign against the complex orientation is `−1`.** On the fibre at `t`, with any complex
structure for which the projection is holomorphic: for every atlas chart `e` and every singular
triangle `σ` that `e` carries to the positively oriented affine triangle with vertices `z`,
`z + ρ`, `z + ρ i` (`ρ > 0`), the transported orientation cycle plus `σ` is a boundary modulo
chains avoiding the barycentre `y = σ b`. So the orientation cycle has local degree `−1` in
`H₂(F, F − y)` at every point: the triangles `A_i` lie clockwise in the chart `ℂ` (between `f_i`
and `e_i ∪ h_i`), and holomorphic maps preserve orientation.
Source: Hatcher, *Algebraic Topology*, §3.3 (local orientations, Theorem 3.26); Forster, §§2–4
(holomorphic maps are orientation preserving); G32 v0.16, Figure 1. -/
theorem hga_fundClass_orientation (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t)) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∀ e : OpenPartialHomeomorph (b63l_parameterFibre mr_base C V hV t) ℂ, e ∈ atlas ℂ (b63l_parameterFibre mr_base C V hV t) →
      ∀ (σ : C(StdSimplex ℝ (Fin 3), (b63l_parameterFibre mr_base C V hV t))) (z : ℂ) (ρ : ℝ), 0 < ρ →
        (∀ a, σ a ∈ e.source) →
        (∀ a, e (σ a) = z + (ρ : ℂ) * (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) →
        ∀ b : StdSimplex ℝ (Fin 3), (∀ k, b.weights k = 1 / 3) →
          ∃ (w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of (b63l_parameterFibre mr_base C V hV t))) 3)
            (u : Simplicial.ChainGroup ℤ
              (TopCat.toSSet.obj (TopCat.of ({σ b}ᶜ : Set (b63l_parameterFibre mr_base C V hV t)))) 2),
            hga_fundChain (hga_fibreMap F V hV t) +
                Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) =
              Simplicial.boundary ℤ 2 w +
                hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2 u :=
  hga_fundClass_orientation_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk

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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t)) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∀ e : OpenPartialHomeomorph (b63l_parameterFibre mr_base C V hV t) ℂ, e ∈ atlas ℂ (b63l_parameterFibre mr_base C V hV t) →
      ∀ (σ : C(StdSimplex ℝ (Fin 3), (b63l_parameterFibre mr_base C V hV t))) (z : ℂ) (ρ : ℝ), 0 < ρ →
        (∀ a, σ a ∈ e.source) →
        (∀ a, e (σ a) = z + (ρ : ℂ) * (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) →
        ∀ b : StdSimplex ℝ (Fin 3), (∀ k, b.weights k = 1 / 3) →
          ∃ (w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of (b63l_parameterFibre mr_base C V hV t))) 3)
            (u : Simplicial.ChainGroup ℤ
              (TopCat.toSSet.obj (TopCat.of ({σ b}ᶜ : Set (b63l_parameterFibre mr_base C V hV t)))) 2),
            hga_fundChain (hga_fibreMap F V hV t) +
                Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) =
              Simplicial.boundary ℤ 2 w +
                hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2 u :=
  hga_fundClass_orientation U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk

/-- **Singular cup product against the intersection form, sign `−1`.** On the fibre at `t`:
if singular `1`-cocycles `φ, ψ` evaluate on every cycle `z` as `Q(P a, P[z])` and `Q(P b, P[z])`,
then `φ ∪ ψ` on the transported orientation cycle is `−Q(P a, P b)`. On a complex-oriented
fundamental cycle the value is `+Q(P a, P b)` (the torus `ℂ/(ℤ + ℤi)` with `a, b` the two
axes fixes this normalization of Poincaré duality); the orientation cycle is minus that cycle
(`hga_fundClass_orientation`).
Source: Hatcher, *Algebraic Topology*, §3.3 (Poincaré duality, cup and intersection products);
Farkas–Kra, *Riemann Surfaces*, Ch. III; `b3_IsIntersectionForm`. -/
theorem hga_aw_intersection (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ] b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t), P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∀ φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (b63l_parameterFibre mr_base C V hV t))) 1,
      φ ∘ₗ Simplicial.boundary ℤ 1 = 0 → ψ ∘ₗ Simplicial.boundary ℤ 1 = 0 →
      ∀ a b : b6m_H1 (b63l_parameterFibre mr_base C V hV t),
        (∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).g.hom,
          φ z.1 = Q (P a) (P (((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).moduleCatHomologyClass z))) →
        (∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).g.hom,
          ψ z.1 = Q (P b) (P (((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).moduleCatHomologyClass z))) →
        Singular.cupCochain (TopCat.of (b63l_parameterFibre mr_base C V hV t)) 1 1 φ ψ
            (hga_fundChain (hga_fibreMap F V hV t)) = -Q (P a) (P b) :=
  hga_aw_intersection_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ] b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t), P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∀ φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (b63l_parameterFibre mr_base C V hV t))) 1,
      φ ∘ₗ Simplicial.boundary ℤ 1 = 0 → ψ ∘ₗ Simplicial.boundary ℤ 1 = 0 →
      ∀ a b : b6m_H1 (b63l_parameterFibre mr_base C V hV t),
        (∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).g.hom,
          φ z.1 = Q (P a) (P (((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).moduleCatHomologyClass z))) →
        (∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).g.hom,
          ψ z.1 = Q (P b) (P (((SingularChainComplex ℤ (TopCat.of (b63l_parameterFibre mr_base C V hV t))).sc 1).moduleCatHomologyClass z))) →
        Singular.cupCochain (TopCat.of (b63l_parameterFibre mr_base C V hV t)) 1 1 φ ψ
            (hga_fundChain (hga_fibreMap F V hV t)) = -Q (P a) (P b) :=
  hga_aw_intersection U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

/-- **Cellular cup form against the intersection form, sign `−1`.** If cellular integral
`1`-cocycles `α, β` of `X̃(b4b_root)` evaluate on every cellular cycle `z` as `I(a, [z])` and
`I(b, [z])`, where `I` is the B3 intersection form of the fibre pulled back through step C's
`hg9_toFibre` (`hga_cellIntersection`), then `hga_cupEval α β = −I(a, b)`. From
`hga_aw_cellular`, `hga_aw_intersection`, the step-C comparison and the extension of cellular
cocycles to singular ones.
Source: Hatcher, *Algebraic Topology*, §3.2–§3.3 and Theorem 2.35; `hg8_H1map_bijective`. -/
theorem hga_cup_intersection (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ] b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t), P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∀ α β : hg2_Edge b4b_Group 13 → ℤ,
      hg2_delta1 ℤ ℤ b4b_root α = 0 → hg2_delta1 ℤ ℤ b4b_root β = 0 →
      ∀ a b : hg2_H1 ℤ b4b_root,
        (∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
          z.1.sum (fun ε n ↦ n * α ε) = hga_cellIntersection F V hV t P Q a (Submodule.Quotient.mk z)) →
        (∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
          z.1.sum (fun ε n ↦ n * β ε) = hga_cellIntersection F V hV t P Q b (Submodule.Quotient.mk z)) →
        hga_cupEval ℤ b4b_root α β = -hga_cellIntersection F V hV t P Q a b :=
  hga_cup_intersection_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ] b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t), P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∀ α β : hg2_Edge b4b_Group 13 → ℤ,
      hg2_delta1 ℤ ℤ b4b_root α = 0 → hg2_delta1 ℤ ℤ b4b_root β = 0 →
      ∀ a b : hg2_H1 ℤ b4b_root,
        (∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
          z.1.sum (fun ε n ↦ n * α ε) = hga_cellIntersection F V hV t P Q a (Submodule.Quotient.mk z)) →
        (∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
          z.1.sum (fun ε n ↦ n * β ε) = hga_cellIntersection F V hV t P Q b (Submodule.Quotient.mk z)) →
        hga_cupEval ℤ b4b_root α β = -hga_cellIntersection F V hV t P Q a b :=
  hga_cup_intersection U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

/-- **The cup form on `H¹_σ` against the geometric Weil–Hermitian form.** There is a nonzero
rational `κ` such that: whenever equivariant cocycles `c, c'` (coefficients `hg4_sigmaK`) evaluate,
in coordinate `0`, on the saturated cellular lattice as the Weil values `h(a, ·)`, `h(b, ·)` of the
pulled-back intersection form (`hga_cellWeil`, `J = 1 + 2Z`), then
`(1 + 2ζ) · hg4_cupForm c c' = κ · h(b, a)`. The order `h(b, a)` is forced: the cup form is
conjugate-linear in `c`, and `c ↦ a` is conjugate-linear. By Schur's lemma both forms come from
the one invariant pairing on the multiplicity space of `σ`; `κ` collects `|G|`, the projector
normalization and the orientation sign, and is real because both sides are Hermitian.
Source: G32 v0.16, Lemma 6.2, Proposition 6.1 and lines 537–548 (comparison up to a rational
scale); Serre, *Linear Representations of Finite Groups*, §2.2; `hg9_isotypic_fibre_comparison`,
`hg4_cupH1_mk`, `hga_cup_intersection`. -/
theorem hga_isotypic_weil (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ] b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t), P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ κ : ℚ, κ ≠ 0 ∧ ∀ (c c' : hg_eqCocycles hg4_sigmaK b4b_root) (a b : hg6_cellLattice),
      (∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec c.1 z.1 0 = hga_cellWeil (hga_cellIntersection F V hV t P Q) a ⟨_, hz⟩) →
      (∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec c'.1 z.1 0 = hga_cellWeil (hga_cellIntersection F V hV t P Q) b ⟨_, hz⟩) →
      (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 c.1 c'.1 =
        (κ : hp_K) * hga_cellWeil (hga_cellIntersection F V hV t P Q) b a :=
  hga_isotypic_weil_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ] b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t), P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ κ : ℚ, κ ≠ 0 ∧ ∀ (c c' : hg_eqCocycles hg4_sigmaK b4b_root) (a b : hg6_cellLattice),
      (∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec c.1 z.1 0 = hga_cellWeil (hga_cellIntersection F V hV t P Q) a ⟨_, hz⟩) →
      (∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec c'.1 z.1 0 = hga_cellWeil (hga_cellIntersection F V hV t P Q) b ⟨_, hz⟩) →
      (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 c.1 c'.1 =
        (κ : hp_K) * hga_cellWeil (hga_cellIntersection F V hV t P Q) b a :=
  hga_isotypic_weil U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

/-! ## Satisfiability and non-degeneracy -/

/-- Joint satisfiability of every binder, constructed from the marked root cover, the existing
lifted cells, the complex structure of the fibre at `mr_base`, B3's intersection form and the
period comparison, all of which have bodies. The fibre is the actual compact surface of the
G32 root cover, not a degenerate space.
Source: `mr_rootCover`, `hg5_lift_existsUnique`, `b63g5_fibre_structure`,
`b3_exists_intersectionForm`, `b6m_period_comparison`. -/
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
    ∃ (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
      (_ : ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t))
      (_ : IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t) ∧
      ∃ (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
          b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
        (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))),
        (∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t),
          P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ) ∧
        b3_IsIntersectionForm ℂ Q ∧ t.val = mr_base := by
  have hb₀ : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    simpa [hg3_arc] using hg3_arc_mem_base 0 0
  let y₀ : b6t_punctured mr_base := ⟨_, hb₀⟩
  have hγ := fun i ↦
    (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose_spec
  set γ := fun i ↦ (mr_loop_existsUnique mr_base hg3_base_mem_polydisc y₀ rfl i).exists.choose
  obtain ⟨U, tU, aU, -, π, hπ, u₀, hroot, C, tC, cC, mC, t2C, compC, conC, aC, -, f, ι, hf, hgal,
    -, hact, hι, hιr, hfι, hιG, -, hrot⟩ := mr_rootCover y₀ γ hγ
  have hL := fun τ ↦ (hg5_lift_existsUnique U π hπ y₀ rfl u₀ C f hf.continuous hgal.2 ι hι hιr hfι
    τ).exists.choose_spec
  let V : Set (Fin 10 → ℂ) := b6t_polydisc mr_base
  have hV : V ⊆ b6t_polydisc mr_base := Set.Subset.rfl
  let t : V := ⟨mr_base, hg3_base_mem_polydisc⟩
  obtain ⟨cs, ms, hk, -⟩ := b63g5_fibre_structure mr_base mr_base_mem_chart C f hf hgal hact V hV t
  obtain ⟨Q, hQ⟩ := b3_exists_intersectionForm (E := ℂ)
    (C := b63l_parameterFibre mr_base C V hV t) (Module.finrank_self ℂ)
  obtain ⟨P, hP⟩ := b6m_period_comparison (b63l_parameterFibre mr_base C V hV t)
  refine ⟨y₀, γ, U, tU, aU, π, hπ, u₀, C, tC, t2C, compC, aC, f, ι, _, rfl, hγ, hroot,
    fun h ↦ (hact h).continuous, hf.continuous, hgal.1, hgal.2, fun j ↦ ?_, hι, hιr, hfι, hιG,
    hL, V, hV, t, cs, ms, hk, P.toLinearMap, Q, hP, hQ, rfl⟩
  obtain ⟨c, hc, hr⟩ := hrot j
  exact ⟨c, hc, hr.2.1.symm⟩

/-- The orientation chain is nonzero: its coefficient on `A_0(1)` is `1`.
Source: `hg2_orient`. -/
example : hg2_orient (G := b4b_Group) (r := 13) (Sum.inl (0, 1)) = 1 := by
  simp only [hg2_orient, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_sub,
    Pi.sub_apply, Finsupp.single_apply, reduceCtorEq, if_false, sub_zero, Sum.inl.injEq,
    Prod.mk.injEq]
  rw [Finset.sum_eq_single (0 : Fin 13) (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- The saturated cellular lattice has rank twelve, so the comparison of statement 6 is not on
a zero lattice.
Source: `hg6_cellLattice_basis`. -/
example : Nonempty (Module.Basis (Fin 12) ℤ hg6_cellLattice) := hg6_cellLattice_basis

/-- The centre on the lattice is not the identity, so `J = 1 + 2Z` is not the scalar `3`.
Source: `hg6_cellCentreL_ne_id`. -/
example : hg6_cellCentreL ≠ LinearMap.id := hg6_cellCentreL_ne_id

open Matrix

/-! ## Chain check toward `g32d_ParabolicPolarization` and `b64b_latticeH` -/

/-- Chain check: for the Shapiro cocycles of H6's `K`-certificate, the geometric Weil values of
their dual lattice vectors have Gram matrix `|G| · g32H0 ζ` up to the nonzero rational `κ` of
`hga_isotypic_weil`. This is the matrix shape, field and scale class used by
`g32d_ParabolicPolarization` and by the determinant class of `b64b_latticeH`; identifying the
dual vectors with a basis of the parameter lattice is the remaining H5/H7 transport.
Source: `hga_isotypic_weil`, `hg4_cupH1_mk`, `hg4_cupH1_shapiro`, `pc_SPar_mk`, `hp_certK_gram`. -/
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
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t),
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    ∃ κ : ℚ, κ ≠ 0 ∧ ∀ (i j : Fin 6) (a b : hg6_cellLattice),
      (∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec (hg4_shapiroZ hg4_sigmaK b4b_root
            ⟨hp_certK i, hg4_sigmaK_tuple ▸ hp_certK_mem i⟩).1 z.1 0 =
          hga_cellWeil (hga_cellIntersection F V hV t P Q) a ⟨_, hz⟩) →
      (∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
          (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec (hg4_shapiroZ hg4_sigmaK b4b_root
            ⟨hp_certK j, hg4_sigmaK_tuple ▸ hp_certK_mem j⟩).1 z.1 0 =
          hga_cellWeil (hga_cellIntersection F V hV t P Q) b ⟨_, hz⟩) →
      (κ : hp_K) * hga_cellWeil (hga_cellIntersection F V hV t P Q) b a =
        (Fintype.card b4b_Group : hp_K) * HodgeLean.Papers.g32H0 pc_zeta i j := by
  intro F
  obtain ⟨κ, hκ, hW⟩ := hga_isotypic_weil U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  refine ⟨κ, hκ, fun i j a b ha hb => ?_⟩
  rw [← hW _ _ a b ha hb]
  have hstar : Function.Semiconj hp_embed star star := by
    intro t
    simp only [hp_embed, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      QuadraticAlgebra.lift_apply_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      zero_mul, add_zero]
    simp [Rat.smul_def]
  have hinv : ∀ x, (hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x = 1 := fun x => by
    apply hg4_embedMatrix_injective
    change ((hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x).map hp_embed = (1 : Matrix _ _ hp_K).map hp_embed
    rw [Matrix.mul_one, Matrix.map_mul, Matrix.conjTranspose_map _ hstar, hg4_sigmaK_map,
      Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  have hprod := b63d_root_product
  have hprodT : (List.ofFn (pc_tuple hg4_sigmaK b4b_root)).prod = 1 := by
    have : List.ofFn (pc_tuple hg4_sigmaK b4b_root) = (List.ofFn b4b_root).map hg4_sigmaK := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, hprod, map_one]
  have hmem : ∀ a, hp_certK a ∈ pc_Z (pc_tuple hg4_sigmaK b4b_root) := fun a =>
    hg4_sigmaK_tuple ▸ hp_certK_mem a
  have hgram : ∀ a b, (1 + 2 * pc_zeta) *
      pc_S (pc_tuple hg4_sigmaK b4b_root) 1 (hp_certK a) (hp_certK b) =
        HodgeLean.Papers.g32H0 pc_zeta a b := by
    rw [hg4_sigmaK_tuple]
    exact hp_certK_gram
  rw [← hg4_cupH1_mk hg4_sigmaK b4b_root hprod 1]
  change (1 + 2 * pc_zeta) * hg4_cupH1 hg4_sigmaK b4b_root 1
      (hg4_shapiroH1 hg4_sigmaK b4b_root (Submodule.Quotient.mk ⟨hp_certK i, hmem i⟩))
      (hg4_shapiroH1 hg4_sigmaK b4b_root (Submodule.Quotient.mk ⟨hp_certK j, hmem j⟩)) = _
  rw [hg4_cupH1_shapiro hg4_sigmaK b4b_root hprod 1 (by simp) hinv,
    pc_SPar_mk _ 1 hprodT (by simp) (fun i => hinv _) _ _ (hmem i) (hmem j), ← hgram i j]
  ring

end HodgeLean.Foundations.Program
