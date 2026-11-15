import HodgeLean.Foundations.Program.PrymParabolicGeometricMarkingGeometry

/-! # Open bodies for the H7 geometric transport
HC no distance; AV milestone no distance. -/

noncomputable section
open Set CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity HodgeLean.Papers HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem hg7g_weil_cup_scale_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
      hfι hιG L hL
    ∃ hskew : ∀ x y, (hg7g_cellForm (hga_cellIntersection F V hV t P Q)).baseChange ℚ (hg7_cellAction.1 x) y =
        -(hg7g_cellForm (hga_cellIntersection F V hV t P Q)).baseChange ℚ x (hg7_cellAction.1 y),
      ∀ x y, hg7g_cellH (hga_cellIntersection F V hV t P Q) hskew x y = (24 : hp_K) * hg7_cellularForm x y := by
  intro F
  have hdeck : ∀ g a b, hga_cellIntersection F V hV t P Q (hg2_H1act ℤ b4b_root g a)
      (hg2_H1act ℤ b4b_root g b) = hga_cellIntersection F V hV t P Q a b := fun g a b ↦
    hga_cellIntersection_deck U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ g a b
  have hZ : ∀ x y, hga_cellIntersection F V hV t P Q (hg6_cellCentre x) (hg6_cellCentre y) =
      hga_cellIntersection F V hV t P Q x y := by
    intro x y
    simpa only [hg6_cellCentre, hg6_centreOf_eq] using hdeck b63d_scalarElement x y
  have hskew := hg7g_cell_skew _ hZ
  refine ⟨hskew, ?_⟩
  exact hg7g_scale_of_gram _
    (hg7g_cellH_left_nondeg _ hskew (hg7g_lattice_nondeg _ hdeck
      (hg7g_cellIntersection_nondeg U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ)))
    (hg7g_gram_of_relation _ hskew
      (hg7g_isotypic_weil24 U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ))

theorem hg7g_cell_discriminant_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
      hfι hιG L hL
    ∃ hskew : ∀ x y, (hg7g_cellForm (hga_cellIntersection F V hV t P Q)).baseChange ℚ (hg7_cellAction.1 x) y =
        -(hg7g_cellForm (hga_cellIntersection F V hV t P Q)).baseChange ℚ x (hg7_cellAction.1 y),
      ∃ hh : (hg7g_cellH (hga_cellIntersection F V hV t P Q) hskew).IsSymm,
      ∃ hn : (hg7g_cellH (hga_cellIntersection F V hV t P Q) hskew).Nondegenerate,
        detClass (hg7g_cellH (hga_cellIntersection F V hV t P Q) hskew) hh hn = classNegTwo := by
  intro F
  obtain ⟨hskew, hscale⟩ := hg7g_weil_cup_scale_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  obtain ⟨hh, hn, hd⟩ := hg7g_class_of_scale _ hscale
  exact ⟨hskew, hh, hn, hd⟩

theorem hg7g_parameter_transport_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
      hfι hιG L hL
    let Λ := b63l_parameterLattice mr_base C hC V hV t
    let E := b63e_singularQ mr_base C hC V hV t P Q
    ∃ A : Λ →ₗ[ℤ] Λ, (∀ x, (A x).val = b63d_operator mr_base C hC V hV t x.val) ∧
    ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
        -E.baseChange ℚ x (A.baseChange ℚ y),
    ∃ hskewC : ∀ x y, (hg7g_cellForm (hga_cellIntersection F V hV t P Q)).baseChange ℚ (hg7_cellAction.1 x) y =
        -(hg7g_cellForm (hga_cellIntersection F V hV t P Q)).baseChange ℚ x (hg7_cellAction.1 y),
    ∃ E₀ : hg6_cellLattice ≃ₗ[ℤ] Λ,
      (∀ x, (E₀ x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
    ∃ e : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction ≃ₗ[hp_K]
        WithJ (ℚ ⊗[ℤ] Λ) ⟨A.baseChange ℚ, hJ⟩,
      (∀ (q : ℚ) (x : hg6_cellLattice),
        WithJ.equiv _ (e ((WithJ.equiv hg7_cellAction).symm (q ⊗ₜ x))) = q ⊗ₜ E₀ x) ∧
      ∀ x y, b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew (e x) (e y) =
        hg7g_cellH (hga_cellIntersection F V hV t P Q) hskewC x y := by
  intro F Λ E
  have hcc : ∃ E₀ : hg6_cellLattice ≃ₗ[ℤ] Λ,
      (∀ x, (E₀ x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x) ∧
      (∀ x, (E₀ (hg6_cellCentreL x) : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) =
        b63d_centre mr_base C hC V hV t (E₀ x)) ∧
      ∀ x, (E₀ (hg6_cellOperator x) : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) =
        b63d_operator mr_base C hC V hV t (E₀ x) :=
    hg9_centre_comparison U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι
      hιG L hL V hV t
  obtain ⟨E₀, h1, -, h3⟩ := hcc
  have hdeck : ∀ g a b, hga_cellIntersection F V hV t P Q (hg2_H1act ℤ b4b_root g a)
      (hg2_H1act ℤ b4b_root g b) = hga_cellIntersection F V hV t P Q a b :=
    fun g a b ↦ hga_cellIntersection_deck U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ g a b
  have hZ : ∀ x y, hga_cellIntersection F V hV t P Q (hg6_cellCentre x) (hg6_cellCentre y) =
      hga_cellIntersection F V hV t P Q x y := by
    intro x y
    simpa only [hg6_cellCentre, hg6_centreOf_eq] using hdeck b63d_scalarElement x y
  have hEB : ∀ a b, E (E₀ a) (E₀ b) = hg7g_cellForm (hga_cellIntersection F V hV t P Q) a b :=
    fun a b ↦ congrArg₂ (fun u v ↦ Q (P u) (P v)) (h1 a) (h1 b)
  exact hg7g_transport_conclusion (M := b6m_H1 (b63l_parameterFibre mr_base C V hV t)) Λ
    (b63d_operator mr_base C hC V hV t) (hg9_toFibre F V hV t)
    (hga_cellIntersection F V hV t P Q) E E₀ h1 h3 hZ hEB

set_option maxHeartbeats 400000 in
theorem hg7g_parameter_discriminant_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    let Λ := b63l_parameterLattice mr_base C hC V hV t
    let E := b63e_singularQ mr_base C hC V hV t P Q
    ∃ A : Λ →ₗ[ℤ] Λ, (∀ x, (A x).val = b63d_operator mr_base C hC V hV t x.val) ∧
    ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
        -E.baseChange ℚ x (A.baseChange ℚ y),
    ∃ hfin : Module.Finite ℤ Λ, haveI := hfin
      ∃ hh : (b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew).IsSymm,
      ∃ hn : (b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew).Nondegenerate,
        detClass (b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew) hh hn = classNegTwo := by
  intro Λ E
  obtain ⟨A, hA, hJ, hskew, hskewC, E₀, -, e, -, he⟩ := hg7g_parameter_transport_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  obtain ⟨_, hh, hn, hd⟩ := hg7g_cell_discriminant_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  obtain ⟨b⟩ := hg6_cellLattice_basis
  have hfin : Module.Finite ℤ Λ := Module.Finite.of_basis (b.map E₀)
  refine ⟨A, hA, hJ, hskew, hfin, ?_⟩
  obtain ⟨hh', hn', hd'⟩ := hg7g_class_transfer _ _ e he hh hn
  exact ⟨hh', hn', hd'.trans hd⟩

set_option maxHeartbeats 400000 in
theorem hg7g_retained_discriminant_aux (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    let Λ := b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
    let E := b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
      (R.P b63gP_s₀) (R.Q b63gP_s₀)
    letI : Module.Finite ℤ Λ := Module.Finite.of_basis (b63gR_basis R)
    ∃ hJ : (R.A b63gP_s₀).baseChange ℚ ∘ₗ (R.A b63gP_s₀).baseChange ℚ =
        (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ ((R.A b63gP_s₀).baseChange ℚ x) y =
        -E.baseChange ℚ x ((R.A b63gP_s₀).baseChange ℚ y),
    ∃ hh : (b64b_latticeH Λ E ⟨(R.A b63gP_s₀).baseChange ℚ, hJ⟩ hskew).IsSymm,
    ∃ hn : (b64b_latticeH Λ E ⟨(R.A b63gP_s₀).baseChange ℚ, hJ⟩ hskew).Nondegenerate,
      detClass (b64b_latticeH Λ E ⟨(R.A b63gP_s₀).baseChange ℚ, hJ⟩ hskew) hh hn =
        classNegTwo := by
  intro Λ E
  have hs := rf8_filling_stabilizers mr_base R.atlas.U R.C R.atlas.π R.atlas.hπ u₀.val R.atlas.f
    R.atlas.ι R.atlas.hι.injective R.atlas.hrange R.atlas.hequiv
  have : FaithfulSMul b4b_Group R.C := hs.1
  have hγ : ∀ i, mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) := fun i ↦
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  have hrot := rf8_cover_roots mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops hγ
    R.atlas.U R.atlas.π R.atlas.hπ u₀ hroot R.C R.atlas.f R.atlas.ι
    R.atlas.hact R.atlas.hf R.atlas.hgal R.atlas.hι.continuous
    R.atlas.hproj R.atlas.hequiv hs.2
  have hstab : ∀ j, ∃ c : R.C, R.atlas.f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j) := fun j ↦ by
    obtain ⟨c, hc, hr⟩ := hrot j
    exact ⟨c, hc, hr.2.1.symm⟩
  have hL := fun τ ↦ (hg5_lift_existsUnique R.atlas.U R.atlas.π R.atlas.hπ b63gP_basePoint rfl u₀
    R.C R.atlas.f R.atlas.hf.continuous R.atlas.hgal.2 R.atlas.ι R.atlas.hι R.atlas.hrange
    R.atlas.hproj τ).exists.choose_spec
  obtain ⟨A, hA, hJ, hskew, hfin, hh, hn, hd⟩ := hg7g_parameter_discriminant_aux R.atlas.U
    R.atlas.π R.atlas.hπ b63gP_basePoint rfl u₀ b63gP_loops hγ hroot R.C R.hC R.atlas.f
    R.atlas.hf.continuous R.atlas.hgal.1 R.atlas.hgal.2 hstab R.atlas.ι R.atlas.hι R.atlas.hrange
    R.atlas.hproj R.atlas.hequiv _ hL (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
    (R.hk b63gP_s₀) (R.P b63gP_s₀) (R.hP b63gP_s₀) (R.Q b63gP_s₀) (R.hQ b63gP_s₀)
  have hAeq : A = R.A b63gP_s₀ :=
    LinearMap.ext fun x ↦ Subtype.ext ((hA x).trans (R.hA b63gP_s₀ x).symm)
  subst hAeq
  exact ⟨hJ, hskew, hh, hn, hd⟩

set_option maxHeartbeats 400000 in
theorem hg7g_rational_marking_aux (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x)) ∧
      ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
        (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
          b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y := by
  have : Module.Free ℤ (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) := Module.Free.of_basis (b63gR_basis R)
  have : Module.Finite ℤ (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) := Module.Finite.of_basis (b63gR_basis R)
  obtain ⟨hJ, hskew, hh, hn, hd⟩ := hg7g_retained_discriminant_aux R u₀ hroot
  have hsig := b64b_geometric_signature mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
    b63gP_s₀ (R.hG b63gP_s₀) mr_base_mem_chart R.atlas.f (R.hk b63gP_s₀) (R.hsurj b63gP_s₀)
    (R.hgal b63gP_s₀) (R.hbranch b63gP_s₀) (R.hrot b63gP_s₀) (R.Q b63gP_s₀) (R.hQ b63gP_s₀)
    (R.P b63gP_s₀) (R.hP b63gP_s₀) (R.A b63gP_s₀) (R.hA b63gP_s₀) hJ hskew
  obtain ⟨e, he⟩ := b64b_standard_isometry_of_invariants _ (b63gR_basis R) _ (R.A b63gP_s₀) hJ
    hskew hh hn hsig hd
  exact b64b_marking_of_standard_isometry _ _ (R.A b63gP_s₀) hJ hskew e he

end HodgeLean.Foundations.Program
