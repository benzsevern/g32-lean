import HodgeLean.Foundations.Program.PrymParabolicGeometricMarkingAlgebra

/-! # Geometric inputs for the H7 geometric transport

On the step-D binders: H4's isotypic duality with its Schur constant `24` (the body of
`hga_isotypic_weil`, restated with the constant explicit and with the duality hypotheses read on
the saturated lattice), and nondegeneracy of the pulled-back intersection form on cellular `H₁`
(unimodularity of the intersection form, bijectivity of the period comparison and of step D).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity HodgeLean.Papers HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.isDefEq.respectTransparency false in
/-- **H4's isotypic duality with the Schur constant `24`.** For cocycles whose `0`-th evaluation
on the saturated lattice is the Weil value of `a`, resp. `b`, the normalized cup form is `24`
times the Weil value of `(b, a)`. This is the argument of `hga_isotypic_weil_aux` with its
constant stated.
Source: G32 v0.16, Proposition 6.1 and lines 537–548; `hga_cup_intersection`,
`hga_cellIntersection_deck`, `hga_coordCup_of_integral_models`,
`hga_isotypic_scale_of_coordinate_duality`. -/
theorem hg7g_isotypic_weil24 (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    ∀ (c c' : hg_eqCocycles hg4_sigmaK b4b_root) (a b : hg6_cellLattice),
      (∀ x : hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root c x 0 =
        hga_cellWeil (hga_cellIntersection F V hV t P Q) a x) →
      (∀ x : hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root c' x 0 =
        hga_cellWeil (hga_cellIntersection F V hV t P Q) b x) →
      (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 c.1 c'.1 =
        24 * hga_cellWeil (hga_cellIntersection F V hV t P Q) b a := by
  intro F c c' a b ha hb
  let B := hga_cellIntersection F V hV t P Q
  have hdeck : ∀ g x y, B (hg2_H1act ℤ b4b_root g x) (hg2_H1act ℤ b4b_root g y) = B x y :=
    hga_cellIntersection_deck U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
  have hcentre : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y := by
    intro x y
    simpa only [hg6_cellCentre, hg6_centreOf_eq] using hdeck b63d_scalarElement x y
  have hJ := hga_cellOperator_skew_of_centre_invariant B hcentre
  have hsk : ∀ x y : hg6_cellLattice, B x y = -B y x := by
    intro x y
    exact hga_cellIntersection_skew F V hV t P Q hQ y x
  obtain ⟨α, hα, eα⟩ := hga_intersection_cocycle F V hV t P Q (hg6_cellOperator a)
  obtain ⟨β, hβ, eβ⟩ := hga_intersection_cocycle F V hV t P Q a
  obtain ⟨η, hη, eη⟩ := hga_intersection_cocycle F V hV t P Q (hg6_cellOperator b)
  obtain ⟨δ, hδ, eδ⟩ := hga_intersection_cocycle F V hV t P Q b
  have hm := hga_coordCup_of_integral_models c c' α β η δ hα hβ
    (fun z ↦ by
      rw [eα z, eβ z]
      exact (congrFun (hg6_evalVec_mk hg4_sigmaK b4b_root c z) 0).symm.trans
        (hga_isotypic_coordinate_evaluation B hdeck c a ha _))
    (fun z ↦ by
      rw [eη z, eδ z]
      exact (congrFun (hg6_evalVec_mk hg4_sigmaK b4b_root c' z) 0).symm.trans
        (hga_isotypic_coordinate_evaluation B hdeck c' b hb _))
  have hc := hga_cup_intersection U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t hk P hP Q hQ
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
  exact hga_isotypic_scale_of_coordinate_duality B hsk hJ c c' a b hcup

/-- **The pulled-back intersection form is nondegenerate on cellular `H₁`.** The intersection
form of the compact fibre is unimodular (`b3_intersectionForm_bijective`), the period comparison
`P` is the bijective one of `b6m_period_comparison` (both agree on smooth loop classes), and
step D's comparison `hg9_toFibre` is bijective (`hg8_H1map_bijective`).
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III; Hatcher, Theorem 2.35;
`b3_intersectionForm_bijective`, `b6m_period_comparison`, `b6m_homology_linearMap_ext`,
`hg8_H1map_bijective`, `hga_lift_pathConnected`. -/
theorem hg7g_cellIntersection_nondeg (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (_hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t),
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr
      hfι hιG L hL
    ∀ u, (∀ z, hga_cellIntersection F V hV t P Q u z = 0) → u = 0 := by
  intro F u hu
  let T := b63l_parameterFibre mr_base C V hV t
  let H : T ≃ₜ C := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  have : PathConnectedSpace C := hga_lift_pathConnected U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  have : PathConnectedSpace T := H.symm.pathConnectedSpace
  have : CompactSpace T := H.symm.compactSpace
  have : T2Space T := H.symm.t2Space
  obtain ⟨P₀, hP₀⟩ := b6m_period_comparison T
  have hPP : P = P₀.toLinearMap :=
    b6m_homology_linearMap_ext T _ P P₀.toLinearMap fun γ ↦ (hP γ).trans (hP₀ γ).symm
  have hQi := (b3_intersectionForm_bijective (E := ℂ) (C := T) (Module.finrank_self ℂ) Q hQ).1
  have hF : Function.Bijective (hg9_toFibre F V hV t) :=
    (b6m_H1Equiv (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm).bijective.comp
      (hg8_H1map_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)
  have hs : Function.Surjective (P ∘ hg9_toFibre F V hV t) := by
    rw [hPP]
    exact P₀.surjective.comp hF.2
  have h0 : Q (P (hg9_toFibre F V hV t u)) = 0 := by
    apply LinearMap.ext
    intro v
    obtain ⟨z, rfl⟩ := hs v
    exact hu z
  have h1 : P (hg9_toFibre F V hV t u) = 0 := hQi (h0.trans (map_zero Q).symm)
  rw [hPP] at h1
  have h2 : hg9_toFibre F V hV t u = 0 := P₀.injective (h1.trans (map_zero P₀).symm)
  exact hF.1 (h2.trans (map_zero _).symm)

end HodgeLean.Foundations.Program
