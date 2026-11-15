import HodgeLean.Foundations.Program.PrymParabolicIntersectionPermutation

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_projection_zero {T : Type} [TopologicalSpace T]
    (y : T) (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : ∀ a, σ a ≠ y) :
    ((relativeChainProjection ℤ (pointComplementPair y)).f 2).hom
      (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)) = 0 := by
  let P := pointComplementPair y
  let σ' : C(StdSimplex ℝ (Fin 3), ({y}ᶜ : Set T)) :=
    ⟨fun a ↦ ⟨σ a, hσ a⟩, σ.continuous.subtype_mk _⟩
  let u := Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ')
  have hu := congrArg (fun m ↦ (m.f 2).hom u)
    (subspaceChainMap_relativeChainProjection ℤ P)
  change ((relativeChainProjection ℤ P).f 2).hom
    ((((chainPairFunctor ℤ).obj P).hom.f 2).hom u) = 0 at hu
  have he : ((((chainPairFunctor ℤ).obj P).hom.f 2).hom u) =
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) := by
    change ((SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) (ModuleCat.of ℤ ℤ)).f 2).hom
      (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ')) = _
    rw [Simplicial.chainOfSimplex_map]
    rfl
  rw [he] at hu
  exact hu

set_option backward.isDefEq.respectTransparency false in
theorem hga_chain2_projection_single {T ι : Type} [TopologicalSpace T]
    (y : T) (σ : ι → C(StdSimplex ℝ (Fin 3), T)) (τ : ι)
    (hσ : ∀ τ', τ' ≠ τ → ∀ a, σ τ' a ≠ y) (c : ι →₀ ℤ) :
    ((relativeChainProjection ℤ (pointComplementPair y)).f 2).hom (hg5_chain2 σ c) =
      c τ • ((relativeChainProjection ℤ (pointComplementPair y)).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (σ τ))) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, Finsupp.add_apply, add_smul, add_zsmul]
  | single τ' n =>
    simp only [hg5_chain2, Finsupp.linearCombination_single]
    erw [LinearMap.map_smul]
    by_cases h : τ' = τ
    · subst τ'
      rw [Finsupp.single_eq_same]
      exact int_smul_eq_zsmul (ModuleCat.isModule
        (((relativeChainFunctor ℤ).obj (pointComplementPair y)).X 2)) n _
    · rw [hga_triangle_projection_zero y (σ τ') (hσ τ' h),
        Finsupp.single_eq_of_ne (Ne.symm h), zero_smul, smul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_zero_weight_face (a : StdSimplex ℝ (Fin 3)) (k : Fin 3)
    (hk : a.weights k = 0) :
    ∃ t : unitInterval, StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t) = a := by
  have hb (j : Fin 3) : a.weights j ≤ 1 := by
    have h0 := a.weights_nonneg 0
    have h1 := a.weights_nonneg 1
    have h2 := a.weights_nonneg 2
    fin_cases j <;> dsimp <;> linarith [hg5_sum3 a]
  fin_cases k <;> dsimp at hk
  · refine ⟨⟨a.weights 2, a.weights_nonneg 2, hb 2⟩, ?_⟩
    apply hg5_simplex_ext <;> rw [hg5_face_w] <;> norm_num <;> linarith [hg5_sum3 a]
  · refine ⟨⟨a.weights 2, a.weights_nonneg 2, hb 2⟩, ?_⟩
    apply hg5_simplex_ext <;> rw [hg5_face_w] <;> norm_num <;> linarith [hg5_sum3 a]
  · refine ⟨⟨a.weights 1, a.weights_nonneg 1, hb 1⟩, ?_⟩
    apply hg5_simplex_ext <;> rw [hg5_face_w] <;> norm_num <;> linarith [hg5_sum3 a]

set_option backward.isDefEq.respectTransparency false in
theorem hga_base_triangle_interior_preimage (τ τ' : hg2_Tri Unit 13)
    (a a' : StdSimplex ℝ (Fin 3)) (ha : ∀ k, 0 < a.weights k)
    (h : hg5_tri τ a = hg5_tri τ' a') : ∀ k, 0 < a'.weights k := by
  intro k
  by_contra hk
  have hzero : a'.weights k = 0 := le_antisymm (not_lt.mp hk) (a'.weights_nonneg k)
  obtain ⟨t, ht⟩ := hga_triangle_zero_weight_face a' k hzero
  have he : hg5_face (hg5_tri τ') k t = hg5_tri τ a :=
    (congrArg (hg5_tri τ') ht).trans h.symm
  fin_cases k
  · exact hg5_open_cells.2.1 τ a ha _ t (he.symm.trans
      (congrArg (fun p : C(unitInterval, OnePoint ℂ) ↦ p t) (hg5_faces τ').1))
  · exact hg5_open_cells.2.1 τ a ha _ t (he.symm.trans
      (congrArg (fun p : C(unitInterval, OnePoint ℂ) ↦ p t) (hg5_faces τ').2.1))
  · exact hg5_open_cells.2.1 τ a ha _ t (he.symm.trans
      (congrArg (fun p : C(unitInterval, OnePoint ℂ) ↦ p t) (hg5_faces τ').2.2))

theorem hga_lift_triangle_avoids {G : Type} [Group G]
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
    ∀ (τ τ' : hg2_Tri G 13) (a : StdSimplex ℝ (Fin 3)), τ' ≠ τ →
      (∀ k, 0 < a.weights k) → ∀ a', L τ' a' ≠ L τ a := by
  intro τ τ' a hne ha a' h
  have he : hg5_tri (hg5_triBase τ) a = hg5_tri (hg5_triBase τ') a' := by
    rw [← (hL τ).1 a, ← (hL τ').1 a']
    exact congrArg f h.symm
  have ha' := hga_base_triangle_interior_preimage _ _ a a' ha he
  exact hne ((hg5_lift_cells U π hπ y₀ hy₀ u₀ C hC f hf hfinv hftr
    ι hι hιr hfι hιG L hL).2 τ' τ a' a ha' ha h).1

set_option backward.isDefEq.respectTransparency false in
theorem hga_fundClass_local_triangle {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T) (τ : hg2_Tri b4b_Group 13)
    (hinj : Function.Injective (F.tri τ))
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (hother : ∀ τ', τ' ≠ τ → ∀ a, F.tri τ' a ≠ F.tri τ b)
    (hcoeff : hg2_orient τ = (1 : ℤ)) :
    (relativeHomologyProjection ℤ (pointComplementPair (F.tri τ b)) 2).hom
      (hga_fundClass F) =
      relativeHomologyMap ℤ 2
        (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap (F.tri τ) hinj b hb)
        (standardComplexLocalClass ℤ 1) := by
  rw [hga_fundClass_pointProjection, ← hga_triangle_localClass (F.tri τ) hinj b hb]
  apply congrArg
    ((((relativeChainFunctor ℤ).obj (pointComplementPair (F.tri τ b))).sc 2).moduleCatHomologyClass)
  apply Subtype.ext
  change ((relativeChainProjection ℤ (pointComplementPair (F.tri τ b))).f 2).hom
      (hg5_chain2 F.tri hg2_orient) = _
  rw [hga_chain2_projection_single _ F.tri τ hother, hcoeff, one_zsmul]

#print axioms hga_fundClass_local_triangle

#print axioms hga_lift_triangle_avoids

#print axioms hga_base_triangle_interior_preimage

#print axioms hga_triangle_zero_weight_face

#print axioms hga_chain2_projection_single

#print axioms hga_triangle_projection_zero
end HodgeLean.Foundations.Program
