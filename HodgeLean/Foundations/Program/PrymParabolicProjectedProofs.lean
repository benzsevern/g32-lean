import HodgeLean.Foundations.Program.PrymParabolicProjectedDefs

/-! # Open bodies for H3b step D
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular Convexity
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

def hg9_restrict {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (e : M ≃ₗ[ℤ] N)
    (p : Submodule ℤ M) (q : Submodule ℤ N) (hm : p.map e.toLinearMap = q) : p ≃+ q where
  toFun x := ⟨e x, hm ▸ Submodule.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨e.symm y, by
    have hy : y.val ∈ p.map e.toLinearMap := hm.symm ▸ y.property
    obtain ⟨x, hx, he⟩ := hy
    have hx' : e.symm y.val = x := by rw [← he]; exact e.symm_apply_apply x
    exact hx' ▸ hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.map_add x y)

theorem hg9_exact_comparison_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
      ∀ x, (E x : b6m_H1 C) = hg8_H1map F x := by
  dsimp only
  let e := LinearEquiv.ofBijective _ (hg8_H1map_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)
  have hm := (hg8_projector_check U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL).2
  refine ⟨(hg9_restrict e _ _ hm).toIntLinearEquiv, ?_⟩
  intro x
  rfl

theorem hg9_saturated_comparison_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
      ∀ x, (E x : b6m_H1 C) = hg8_H1map F x := by
  dsimp only
  let e := LinearEquiv.ofBijective _ (hg8_H1map_bijective U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL)
  have he := hg8_H1map_deck U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  have hm := (hg6_saturated_transport (hg2_H1act ℤ b4b_root)
    (fun h ↦ homologyMap ℤ 1 (TopCat.ofHom (⟨fun c : C ↦ h • c, hC h⟩ : C(C,C)))) e he).1
  refine ⟨(hg9_restrict e _ _ hm).toIntLinearEquiv, ?_⟩
  intro x
  rfl

theorem hg9_fibre_exact_comparison_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
      ∀ x, (E x : b6m_H1 (b63l_parameterFibre mr_base C V hV t)) = hg9_toFibre F V hV t x := by
  dsimp only
  obtain ⟨e, he, hd, -, -⟩ := hg8_parameterLattice_check U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t
  have hc : e.toLinearMap ∘ₗ hg2_projector =
      b63l_fibreOperator mr_base C hC ⟨t.val, hV t.property⟩ ∘ₗ e.toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg2_projector, b63l_fibreOperator, b63l_homologyOperator,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, hd]
    rfl
  have hm : (LinearMap.range hg2_projector).map e.toLinearMap =
      b63l_fibreScaledImage mr_base C hC ⟨t.val, hV t.property⟩ := by
    rw [← LinearMap.range_comp, hc, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr e.surjective, Submodule.map_top]
  refine ⟨(hg9_restrict e _ _ hm).toIntLinearEquiv, ?_⟩
  intro x
  exact he x

theorem hg9_parameterLattice_map_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    hg6_cellLattice.map (hg9_toFibre F V hV t) = b63l_parameterLattice mr_base C hC V hV t := by
  dsimp only
  obtain ⟨e, he, -, hm, -⟩ := hg8_parameterLattice_check U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t
  have heq : e.toLinearMap = hg9_toFibre _ V hV t := LinearMap.ext he
  rw [← heq]
  exact hm

theorem hg9_centre_comparison_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        b63d_operator mr_base C hC V hV t (E x) := by
  dsimp only
  obtain ⟨e, he, hd, hm, hc⟩ := hg8_parameterLattice_check U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t
  let E : hg6_cellLattice ≃ₗ[ℤ] b63l_parameterLattice mr_base C hC V hV t :=
    (hg9_restrict e _ _ hm).toIntLinearEquiv
  have hval (x) : (E x : b6m_H1 _) = e x := rfl
  refine ⟨E, fun x ↦ (hval x).trans (he x), ?_, ?_⟩
  · intro x
    rw [hval, hval]
    exact hc x
  · intro x
    rw [hval, hval]
    change e (x.val + (2 : ℤ) • hg6_cellCentre x.val) = _
    rw [map_add, map_zsmul, hc]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, ofNat_zsmul]

theorem hg9_not_deck_stable_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
        (hg9_toFibre F V hV t x) ∉ b63l_parameterLattice mr_base C hC V hV t := by
  dsimp only
  obtain ⟨e, he, hd, hm, -⟩ := hg8_parameterLattice_check U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t
  obtain ⟨h, x, hx, hn⟩ := hg6_lattice_not_deck_stable
  refine ⟨h, x, hx, hn, ?_⟩
  change homologyMap ℤ 1 _ (b6m_H1Equiv _ (hg8_H1map _ x)) ∉ _
  rw [← he, ← hd, ← hm]
  intro hy
  obtain ⟨z, hz, hez⟩ := hy
  exact hn ((e.injective hez) ▸ hz)

theorem hg9_isotypic_fibre_comparison_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
            ((1 : ℚ) ⊗ₜ[ℤ] E ⟨Submodule.Quotient.mk z, hz⟩) = hg6_pairVec c.1 z.1 0 := by
  dsimp only
  obtain ⟨E, hE, -, -⟩ := hg9_centre_comparison_aux U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL V hV t
  obtain ⟨Θ, hi, hr, hv⟩ := hg6_isotypic_comparison
  let q := E.baseChange ℤ ℚ
  let T : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K]
      ((ℚ ⊗[ℤ] b63l_parameterLattice mr_base C hC V hV t) →ₗ[ℚ] hp_K) :=
    { toFun := fun c ↦ (Θ c).comp q.symm.toLinearMap
      map_add' := fun x y ↦ by
        apply LinearMap.ext
        intro z
        exact congrArg (fun f ↦ f (q.symm z)) (Θ.map_add x y)
      map_smul' := fun r x ↦ by
        apply LinearMap.ext
        intro z
        exact congrArg (fun f ↦ f (q.symm z)) (Θ.map_smul r x) }
  have hT (c) (x) : T c (q x) = Θ c x := by
    change Θ c (q.symm (q x)) = _
    rw [q.symm_apply_apply]
  refine ⟨E, hE, T, ?_, ?_, ?_⟩
  · intro x y h
    apply hi
    apply LinearMap.ext
    intro z
    exact (hT x z).symm.trans ((congrArg (fun f ↦ f (q z)) h).trans (hT y z))
  · intro φ
    constructor
    · rintro ⟨c, rfl⟩ x
      change T c (q (hg6_cellJ x)) = QuadraticAlgebra.omega * T c (q x)
      rw [hT, hT]
      exact (hr (Θ c)).mp ⟨c, rfl⟩ x
    · intro h
      have hh : φ.comp q.toLinearMap ∈ LinearMap.range Θ := (hr _).mpr h
      obtain ⟨c, hc⟩ := hh
      refine ⟨c, ?_⟩
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := q.surjective y
      rw [hT]
      exact congrArg (fun f ↦ f x) hc
  · intro c z hz
    have hx := hT (Submodule.Quotient.mk c)
      ((1 : ℚ) ⊗ₜ[ℤ] (⟨Submodule.Quotient.mk z, hz⟩ : hg6_cellLattice))
    exact hx.trans (hv c z hz)

end HodgeLean.Foundations.Program
