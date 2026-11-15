import HodgeLean.Foundations.Program.PrymParabolicIntersectionCap
import HodgeLean.Foundations.Program.PrymParabolicIntersectionIsotypicModels
import HodgeLean.Foundations.Program.PrymParabolicIntersectionDeck
import HodgeLean.Foundations.Program.PrymParabolicIntersectionIntegralCup
import HodgeLean.Foundations.Program.PrymParabolicIntersectionFaces
import HodgeLean.Foundations.Program.PrymParabolicIntersectionWeilAlgebra
import HodgeLean.Foundations.Program.PrymParabolicIntersectionConnected
import HodgeLean.Foundations.Program.PrymParabolicIntersectionWedgeDegree
import HodgeLean.Foundations.Program.PrymParabolicIntersectionLocalization
import HodgeLean.Foundations.Program.PrymParabolicIntersectionFibreDuality

/-! # Open bodies for stage H4, geometric part, first stage
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity HodgeLean.Foundations
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem hga_aw_cellular_aux {G : Type} [Group G] [Fintype G] {r : ℕ} {g : Fin r → G} {T : Type}
    [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1) :
    Singular.cupCochain (TopCat.of T) 1 1 φ ψ (hg5_chain2 F.tri hg2_orient) =
      hga_cupEval ℤ g (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1)))
        (fun ε ↦ ψ (hg5_chain1 F.edge (Finsupp.single ε 1))) := by
  classical
  have hfront : Simplicial.frontInclusion 1 1 = SimplexCategory.δ (2 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  have hback : Simplicial.backInclusion 1 1 = SimplexCategory.δ (0 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  unfold hg5_chain2 hga_cupEval
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul,
    Singular.cupCochain_apply_simplex, hg5_chain1, Finsupp.sum_single_index,
    zero_smul, one_smul, Simplicial.frontFace, Simplicial.backFace, hfront, hback]
  apply Finsupp.sum_congr
  intro τ n
  rw [show (TopCat.toSSet.obj (TopCat.of T)).map (SimplexCategory.δ (2 : Fin 3)).op
      (b3Rest2_triSimplex (F.tri τ)) = b3Rest2_pathSimplex (F.edge (hg2_face2 τ)) from
        (hg5_delta_face (F.tri τ) 2).trans (congrArg b3Rest2_pathSimplex (F.faces τ).2.2)]
  rw [show (TopCat.toSSet.obj (TopCat.of T)).map (SimplexCategory.δ (0 : Fin 3)).op
      (b3Rest2_triSimplex (F.tri τ)) = b3Rest2_pathSimplex (F.edge (hg2_face0 g τ)) from
        (hg5_delta_face (F.tri τ) 0).trans (congrArg b3Rest2_pathSimplex (F.faces τ).1)]
  rfl

theorem hga_fundClass_generator_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    ∃ e : Homology ℤ (TopCat.of C) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1 := by
  have he := hg8_edgeRel_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot
    C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  have ht := hg8_triRel_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot
    C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  exact hga_generator_from_skeleta _ (he.2 2 (by omega)) ht.1 he.1.1

set_option backward.isDefEq.respectTransparency false in
theorem hga_fundClass_orientation_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
                hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2 u := by
  intro F e he σ z ρ hρ hσ hform b hb
  let T := b63l_parameterFibre mr_base C V hV t
  let H : T ≃ₜ C := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  letI : PathConnectedSpace C := hga_lift_pathConnected U π hπ y₀ hy₀ u₀ γ hγ hroot
    C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  letI : PathConnectedSpace T := H.symm.pathConnectedSpace
  letI : CompactSpace T := H.symm.compactSpace
  letI : T2Space T := H.symm.t2Space
  let D := hga_fibreMap F V hV t
  let τ : hg2_Tri b4b_Group 13 := Sum.inl (0, 1)
  let b₀ := hga_triangleRetraction 0
  have hb₀ : ∀ i, b₀.weights i = 1 / 3 := hga_triangleRetraction_zero_weights
  have hp₀ : ∀ i, 0 < b₀.weights i := by intro i; rw [hb₀]; norm_num
  have hinj : Function.Injective (D.tri τ) := by
    intro a a' h
    apply hg5_tri_injective (hg5_triBase τ)
    rw [← (hL τ).1 a, ← (hL τ).1 a']
    exact congrArg f (H.symm.injective h)
  have hother : ∀ τ', τ' ≠ τ → ∀ a, D.tri τ' a ≠ D.tri τ b₀ := by
    intro τ' hne a h
    have h' : L τ' a = L τ b₀ := H.symm.injective h
    exact hga_lift_triangle_avoids U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr
      ι hι hιr hfι hιG L hL τ τ' b₀ hne hp₀ a h'
  have hcoeff : hg2_orient τ = (1 : ℤ) := (hg2_orient_coeffs 0 (1 : b4b_Group)).1
  have huv : hg3_waist 0 < hg5_markRe 0 := by norm_num [hg3_waist, hg5_markRe]
  have hσproj : ∀ a, f (L τ a) = hg5_tri (Sum.inl (0, ())) a := (hL τ).1
  have hproj := hga_firstLift_projection f (L τ) hσproj V hV t
  have hplane : ∀ᶠ w : ℂ in 𝓝 0, b63d_projection mr_base C f V hV t
      (hga_wedgeLift (D.tri τ) (hg3_waist 0) (hg5_markRe 0) w) =
      ((w + (-37 / 3) : ℂ) : OnePoint ℂ) := by
    filter_upwards [hproj] with w hw
    change b63d_projection mr_base C f V hV t
      (H.symm (hga_wedgeLift (L τ) (hg3_waist 0) (hg5_markRe 0) w)) = _
    convert hw using 1 <;> congr 2 <;> ring
  have hlocal : (relativeHomologyProjection ℤ (pointComplementPair (D.tri τ b₀)) 2).hom
      (hga_fundClass D) = -b6m_surfaceLocalClass ℤ (D.tri τ b₀) :=
    (hga_fundClass_local_triangle D τ hinj b₀ hb₀ hother hcoeff).trans
      (hga_wedgeLift_localClass (D.tri τ) hinj _ _ huv
        (b63d_projection mr_base C f V hV t) hk (-37 / 3) hplane)
  have hall := hga_surface_class_of_one_local_value (hga_fundClass D) (-1) _
    (by simpa only [neg_one_zsmul] using hlocal)
  exact hga_orientation_boundary_of_local_projection D σ b hb e he hσ z ρ hρ.ne' hform
    (by simpa only [neg_one_zsmul] using hall (σ b))

theorem hga_aw_intersection_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
            (hga_fundChain (hga_fibreMap F V hV t)) = -Q (P a) (P b) := by
  intro F φ ψ hφ hψ a b ha hb
  exact hga_aw_intersection_of_duality (hga_fibreMap F V hV t) P Q hQ φ ψ hφ hψ a b ha hb
    (fun z ↦ hga_fibre_duality U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
      hfι hιG L hL V hV t hk P hP Q hQ φ hφ z)

theorem hga_cup_intersection_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        hga_cupEval ℤ b4b_root α β = -hga_cellIntersection F V hV t P Q a b := by
  intro F α β hα hβ a b ha hb
  let D := hga_fibreMap F V hV t
  let A := hg9_toFibre F V hV t a
  let B := hg9_toFibre F V hV t b
  obtain ⟨φ, hφ, heφ⟩ := hga_singular_cocycle_of_functional
    (TopCat.of (b63l_parameterFibre mr_base C V hV t)) ((Q (P A)).comp P)
  obtain ⟨ψ, hψ, heψ⟩ := hga_singular_cocycle_of_functional
    (TopCat.of (b63l_parameterFibre mr_base C V hV t)) ((Q (P B)).comp P)
  let α' := fun ε ↦ φ (hg5_chain1 D.edge (Finsupp.single ε 1))
  let β' := fun ε ↦ ψ (hg5_chain1 D.edge (Finsupp.single ε 1))
  have hα' : hg2_delta1 ℤ ℤ b4b_root α' = 0 := hga_restriction_cocycle D φ hφ
  have hevalφ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root)) :
      z.1.sum (fun ε n ↦ n * α' ε) = hga_cellIntersection F V hV t P Q a (Submodule.Quotient.mk z) := by
    rw [← hga_cochain_chain1 D φ]
    have h := heφ (hg8_cycle1 D z)
    change φ (hg5_chain1 D.edge z.1) = Q (P A) (P (hg8_H1map D (Submodule.Quotient.mk z))) at h
    rw [hga_H1map_fibre] at h
    exact h
  have hevalψ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root)) :
      z.1.sum (fun ε n ↦ n * β' ε) = hga_cellIntersection F V hV t P Q b (Submodule.Quotient.mk z) := by
    rw [← hga_cochain_chain1 D ψ]
    have h := heψ (hg8_cycle1 D z)
    change ψ (hg5_chain1 D.edge z.1) = Q (P B) (P (hg8_H1map D (Submodule.Quotient.mk z))) at h
    rw [hga_H1map_fibre] at h
    exact h
  have heq := hga_cupEval_eq_of_cycle_evaluations α α' β β' hα' hβ
    (fun z ↦ (ha z).trans (hevalφ z).symm) (fun z ↦ (hb z).trans (hevalψ z).symm)
  rw [heq]
  rw [← hga_aw_cellular_aux D φ ψ]
  exact hga_aw_intersection_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ φ ψ hφ hψ A B heφ heψ

set_option backward.isDefEq.respectTransparency false in
theorem hga_isotypic_weil_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        (κ : hp_K) * hga_cellWeil (hga_cellIntersection F V hV t P Q) b a := by
  intro F
  refine ⟨24, by norm_num, ?_⟩
  intro c c' a b ha hb
  let B := hga_cellIntersection F V hV t P Q
  have hdeck : ∀ g x y, B (hg2_H1act ℤ b4b_root g x) (hg2_H1act ℤ b4b_root g y) = B x y :=
    hga_cellIntersection_deck U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab
      ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  have hcentre : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y := by
    intro x y
    simpa only [hg6_cellCentre, hg6_centreOf_eq] using hdeck b63d_scalarElement x y
  have hJ := hga_cellOperator_skew_of_centre_invariant B hcentre
  have hsk : ∀ x y : hg6_cellLattice, B x y = -B y x := by
    intro x y
    exact hga_cellIntersection_skew F V hV t P Q hQ y x
  have hdual (d : hg_eqCocycles hg4_sigmaK b4b_root) (u : hg6_cellLattice)
      (hd : ∀ (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
        (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        hg6_pairVec d.1 z.1 0 = hga_cellWeil B u ⟨_, hz⟩) :
      ∀ x : hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root d x 0 = hga_cellWeil B u x := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    exact (congrFun (hg6_evalVec_mk hg4_sigmaK b4b_root d z) 0).trans (hd z hx)
  obtain ⟨α, hα, eα⟩ := hga_intersection_cocycle F V hV t P Q (hg6_cellOperator a)
  obtain ⟨β, hβ, eβ⟩ := hga_intersection_cocycle F V hV t P Q a
  obtain ⟨η, hη, eη⟩ := hga_intersection_cocycle F V hV t P Q (hg6_cellOperator b)
  obtain ⟨δ, hδ, eδ⟩ := hga_intersection_cocycle F V hV t P Q b
  have hm := hga_coordCup_of_integral_models c c' α β η δ hα hβ
    (fun z ↦ by
      rw [eα z, eβ z]
      exact (congrFun (hg6_evalVec_mk hg4_sigmaK b4b_root c z) 0).symm.trans
        (hga_isotypic_coordinate_evaluation B hdeck c a (hdual c a ha) _))
    (fun z ↦ by
      rw [eη z, eδ z]
      exact (congrFun (hg6_evalVec_mk hg4_sigmaK b4b_root c' z) 0).symm.trans
        (hga_isotypic_coordinate_evaluation B hdeck c' b (hdual c' b hb) _))
  have hc := hga_cup_intersection_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  rw [hc α η hα hη _ _ eα eη, hc α δ hα hδ _ _ eα eδ,
    hc β η hβ hη _ _ eβ eη, hc β δ hβ hδ _ _ eβ eδ] at hm
  change hg6_coordCup b4b_root 0 0 c.1 c'.1 =
    ((-B (hg6_cellOperator a) (hg6_cellOperator b) : ℤ) : hp_K) -
      QuadraticAlgebra.omega * ((-B (hg6_cellOperator a) b : ℤ) : hp_K) +
      QuadraticAlgebra.omega * ((-B a (hg6_cellOperator b) : ℤ) : hp_K) +
      3 * ((-B a b : ℤ) : hp_K) at hm
  rw [hga_cellOperator_bilinear B hJ a b, hJ a b] at hm
  have hcup : hg6_coordCup b4b_root 0 0 c.1 c'.1 =
      -6 * ((B a b : ℤ) : hp_K) -
        2 * QuadraticAlgebra.omega * ((B a (hg6_cellOperator b) : ℤ) : hp_K) := by
    rw [hm]
    push_cast
    ring
  simpa only [Rat.cast_ofNat] using
    hga_isotypic_scale_of_coordinate_duality B hsk hJ c c' a b hcup


end HodgeLean.Foundations.Program
