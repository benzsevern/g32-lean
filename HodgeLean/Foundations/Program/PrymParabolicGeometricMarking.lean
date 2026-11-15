import HodgeLean.Foundations.Program.PrymParabolicGeometricMarkingProofs

/-! # H7 geometric transport: the geometric discriminant and the rational marking

Each statement is an implication. Statements 1–4 start from the step-D binders of the marked root
cover (the quotient covering, the filling, the lifted triangles) and, on a parameter fibre, a
complex structure with holomorphic projection, a period comparison and a B3 intersection form:
the binders of `hga_isotypic_weil`. Statements 5–6 start from the retained family
`R : rf8_SharedFamily` at `b63gP_s₀` with based root monodromy `u₀`, `hroot`.

Claimed: (1) the geometric Weil form on the saturated cellular lattice is 24 times H7's certified cup-dual form `hg7_cellularForm`; (2) its determinant class is `[−2]`;
(3) step D's equivalence carries it isometrically to the Weil form of `b63e_singularQ` on the
rational parameter lattice; (4) that form has class `[−2]`; (5) the same on the retained family
with `R.A b63gP_s₀`; (6) the rational marking `m` with the action and pairing identities of
`b64e_hisog` and `b63gR_periodMap`. Not claimed: the B5-model normalization, `hpol` or any statement on the universal family.
HC no distance; AV milestone no distance.
-/

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

/-- **The geometric Weil form is 24 times the cellular cup-dual form.** On a parameter
fibre of the marked root cover, the Weil–Hermitian form of the pulled-back intersection form
`hga_cellIntersection`, restricted to the saturated coordinate lattice, is skew for `J = 1 + 2Z`,
and equals `24` times H7's cup-dual form `hg7_cellularForm` on `ℚ ⊗ hg6_cellLattice`,
using the Schur constant chosen by `hga_isotypic_weil_aux`.
Source: G32 v0.16, Proposition 6.1 and lines 537–548; Bourbaki, *Algebra*, Ch. IX, §1 (dual
sesquilinear forms); `hga_isotypic_weil`, `hg8_H1map_bijective`, `hg7_evaluation_bijective`,
`hg6_coordCup_schur`. -/
theorem hg7g_weil_cup_scale (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
      ∀ x y, hg7g_cellH (hga_cellIntersection F V hV t P Q) hskew x y = (24 : hp_K) * hg7_cellularForm x y :=
  hg7g_weil_cup_scale_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

example := @hg7g_weil_cup_scale

/-- **The geometric discriminant on the saturated cellular lattice.** The geometric Weil form on
`ℚ ⊗ hg6_cellLattice` is Hermitian and nondegenerate, and its determinant class modulo norms of
`ℚ(√−3)` is `[−2]`.
Source: G32 v0.16, proof of Proposition 6.3; `hg7_cellular_discriminant`, `hg7_scale_class`,
`hg7_cellular_hermitian`. -/
theorem hg7g_cell_discriminant (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        detClass (hg7g_cellH (hga_cellIntersection F V hV t P Q) hskew) hh hn = classNegTwo :=
  hg7g_cell_discriminant_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

example := @hg7g_cell_discriminant

/-- **Transport to the saturated singular lattice.** The centre-compatible equivalence of step D
(`hg9_centre_comparison`) extends to a `K`-linear isometry from the geometric Weil form on
`ℚ ⊗ hg6_cellLattice` to the Weil form `b64b_latticeH` of `b63e_singularQ` on the rational
parameter lattice, with the restricted operator `A` of `b63d_operator` acting as `√−3`.
Source: `hg9_centre_comparison`, `hg6_cellOperator_sq`, `b63e_singularQ`; Bourbaki, *Algebra*,
Ch. II, §5 (extension of scalars). -/
theorem hg7g_parameter_transport (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        hg7g_cellH (hga_cellIntersection F V hV t P Q) hskewC x y :=
  hg7g_parameter_transport_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

example := @hg7g_parameter_transport

/-- **The geometric discriminant on the saturated singular lattice.** On the parameter fibre, the
Weil form of `b63e_singularQ` on the rational parameter lattice, with `A` acting as `√−3`, is
Hermitian and nondegenerate with determinant class `[−2]`. This is the shape of B6-4b's set-aside
`b64b_marked_lattice_discriminant`, on the step-D binders.
Source: G32 v0.16, proof of Proposition 6.3; `hg7g_parameter_transport`,
`hg7g_cell_discriminant`, `HermitianClass.detClass_eq_of_equiv`. -/
theorem hg7g_parameter_discriminant (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        detClass (b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew) hh hn = classNegTwo :=
  hg7g_parameter_discriminant_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ

example := @hg7g_parameter_discriminant

/-- **The geometric discriminant on the retained family at the reference point.** For the retained
family with based root monodromy, the Weil form of `b63e_singularQ` on the rational parameter
lattice at `b63gP_s₀`, with the family's restricted operator `R.A b63gP_s₀` acting as `√−3`, has
determinant class `[−2]`. This is the discriminant shared by `hpol` and `b64_lattice_discriminant`.
Source: G32 v0.16, proof of Proposition 6.3; `hg7g_parameter_discriminant`, `b63gR_basis`,
`rf8_filling_stabilizers`, `hg5_lift_existsUnique`. -/
theorem hg7g_retained_discriminant (R : rf8_SharedFamily)
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
        classNegTwo :=
  hg7g_retained_discriminant_aux R u₀ hroot

example := @hg7g_retained_discriminant

/-- **The rational marking of the retained reference fibre.** For the retained family with based
root monodromy there is a rational linear equivalence `m` from the saturated parameter lattice at
`b63gP_s₀` to `ℚ ⊗ b60_Lattice` carrying `R.A b63gP_s₀` to `b60_omega` and the rationalized
`b63e_singularQ` exactly to `b60_E`: the binders `m`, `hJ`, `hpair` of `b64e_hisog` and
`b63gR_periodMap`.
Source: G32 v0.16, §6 and Proposition 6.3; Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245–248;
`hg7g_retained_discriminant`, `b64b_lattice_signature`, `HermitianClass.hermClass_rank_six_standard`. -/
theorem hg7g_rational_marking (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x)) ∧
      ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
        (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
          b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y :=
  hg7g_rational_marking_aux R u₀ hroot

example := @hg7g_rational_marking

/-! ## Satisfiability and non-degeneracy -/

/-- Joint satisfiability of the binders of statements 1–4, constructed as in H4's check from the
marked root cover, the existing lifted cells, the complex structure of the fibre at `mr_base`,
B3's intersection form and the period comparison, all of which have bodies. The fibre is the
actual compact surface of the G32 root cover.
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

/-- Satisfiability of the binders of statements 5–6 on the retained family, with integral rank
twelve and a nonidentity root, using only existing statements with bodies.
Source: `rf8_shared_root`, `mr_loop_existsUnique`, `b63gR_basis`, `b63_root_order`. -/
example : ∃ (R : rf8_SharedFamily) (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint}),
    (∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) ∧
    Module.finrank ℤ (b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀) = 12 ∧ b4b_root 0 ≠ 1 := by
  obtain ⟨R, y₀, γ, u₀, hγ, hroot⟩ := rf8_shared_root
  have hy : y₀ = b63gP_basePoint := by
    apply Subtype.ext
    obtain ⟨p, hp, -⟩ := hγ 12
    calc
      (y₀ : OnePoint ℂ) = mr_curve 12 0 := by simpa using hp 0
      _ = (b63gP_basePoint : OnePoint ℂ) := by
        change mr_curve 12 0 = ((mr_basePoint : ℂ) : OnePoint ℂ)
        simp [mr_curve, mr_outer, mr_basePoint]
  subst y₀
  have hγeq : γ = b63gP_loops := by
    funext i
    exact (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique
      (hγ i) (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  subst γ
  refine ⟨R, u₀, hroot, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin]
  · intro h
    have ho := b63_root_order (0 : Fin 13)
    rw [h, orderOf_one] at ho
    norm_num at ho

/-- The saturated cellular lattice has rank twelve, its rationalization has `K`-dimension six,
and the centre is not the identity, so `J = 1 + 2Z` is not a scalar: statements 1–3 are not about
a zero lattice or the trivial centre.
Source: `hg6_cellLattice_finrank`, `b64b_rank_six`, `hg6_cellCentreL_ne_id`. -/
example : Module.finrank ℤ hg6_cellLattice = 12 ∧
    Module.finrank hp_K (WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) = 6 ∧
    hg6_cellCentreL ≠ LinearMap.id :=
  ⟨hg6_cellLattice_finrank,
    b64b_rank_six _ (Classical.choice hg6_cellLattice_basis) hg7_cellAction,
    hg6_cellCentreL_ne_id⟩

/-- The comparison form of statement 1 is nondegenerate of signature `(3, 3)`, so a nonzero
multiple of it is not the zero form.
Source: `hg7_cellular_hermitian`, `hg7_cellular_signature`. -/
example : hg7_cellularForm.Nondegenerate ∧ hermSignature hg7_cellularForm = (3, 3) :=
  ⟨hg7_cellular_hermitian.2, hg7_cellular_signature⟩

/-- The target of the marking of statement 6 has the same class `[−2]` and signature `(3, 3)`.
Source: `detClass_diag_F1569`, `hermSignature_diag_F1569`. -/
example : detClass b60_H (diagForm_isSymm _) (diagForm_nondegenerate diag_F1569_ne_zero) =
      classNegTwo ∧ hermSignature b60_H = (3, 3) :=
  ⟨detClass_diag_F1569, hermSignature_diag_F1569⟩

/-- Falsification of a signature-only route: the diagonal form `(1, 1, 1, −1, −1, −1)` has class
`[−1] ≠ [−2]`, so statements 2, 4 and 5 carry information beyond rank and signature.
Source: `hp_diag_neg_one_detClass`, `hp_class_neg_one_ne_neg_two`. -/
example : detClass (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -1]) (diagForm_isSymm _)
      (diagForm_nondegenerate hp_diag_neg_one_ne_zero) ≠ classNegTwo := by
  rw [hp_diag_neg_one_detClass]
  exact hp_class_neg_one_ne_neg_two

/-! ## Chain checks -/

/-- Statement 6 supplies the marking binders of `b64e_hisog`, hence the fibre isogenies at every
parameter in the period domain.
Source: `hg7g_rational_marking`, `b64e_hisog`. -/
example (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (Fm : g32m_UniversalFamily) (hFm : Fm.univ = b60b_univ) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      ∀ (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain),
        g32t_KIsog ((b63gR_family R).fiber t) (Fm.univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩) := by
  obtain ⟨m, hJ, hpair⟩ := hg7g_rational_marking R u₀ hroot
  exact ⟨m, b64e_hisog R m hJ hpair Fm hFm⟩

/-- Statement 6 with `b64e_hisog` fills the marking and isogeny binders of `b63gR_periodMap`; only
the curve, the certified jet and the codifferential comparison remain.
Source: `hg7g_rational_marking`, `b64e_hisog`, `b63gR_periodMap`. -/
example (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (Fm : g32m_UniversalFamily) (hFm : Fm.univ = b60b_univ) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      ∀ (curve : ℂ → Fin 10 → ℂ) (_ : ContinuousAt curve 0)
        (_ : curve 0 ∈ b6t_polydisc mr_base)
        (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (_ : g32r_CertifiedJet jet)
        (_ : ∀ᶠ θ in nhds (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
          ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
            jet θ = L * LinearMap.toMatrix'
              (fderiv ℂ (b64i_period R b63gP_s₀ m) (curve θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T),
        ∃ F : g32r_PeriodMap Fm (b63gR_family R),
          F.V = b6t_polydisc mr_base ∧ F.period = b64i_period R b63gP_s₀ m := by
  obtain ⟨m, hJ, hpair⟩ := hg7g_rational_marking R u₀ hroot
  exact ⟨m, fun curve hc h0 jet hjet hcod => b63gR_periodMap R m hJ hpair Fm
    (b64e_hisog R m hJ hpair Fm hFm) curve hc h0 jet hjet hcod⟩

end HodgeLean.Foundations.Program
