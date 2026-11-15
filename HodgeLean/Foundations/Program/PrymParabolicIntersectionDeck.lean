import HodgeLean.Foundations.Program.PrymParabolicIntersectionWedgeDegree
import HodgeLean.Foundations.Program.PrymParabolicIntersectionDefs
import HodgeLean.Foundations.Program.PrymParabolicIntersectionConnected
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cIntersection

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem hga_nonconstant_of_plane_lift {T : Type} [TopologicalSpace T]
    (e : C(ℂ, T)) (k : T → OnePoint ℂ) (c : ℂ)
    (hp : ∀ᶠ z : ℂ in 𝓝 0, k (e z) = ((z + c : ℂ) : OnePoint ℂ)) :
    ∃ p q, k p ≠ k q := by
  obtain ⟨S, hS, hSo, h0⟩ := mem_nhds_iff.mp hp
  obtain ⟨x, hx, y, hy, hxy⟩ := (infinite_of_mem_nhds (0 : ℂ) (hSo.mem_nhds h0)).nontrivial
  refine ⟨e x, e y, fun h ↦ hxy ?_⟩
  rw [hS hx, hS hy] at h
  exact add_right_cancel (OnePoint.coe_injective h)

/-- Deck transformations in the topological marking as homeomorphisms.
Source: Harris–Morrison, *Moduli of Curves*, §1.G. -/
def hga_deckHomeomorph (b : Fin 10 → ℂ) (G C : Type) [Group G]
    [TopologicalSpace C] [MulAction G C]
    (hC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (g : G) : b6m_Fibre b C t ≃ₜ b6m_Fibre b C t :=
  let H := b6m_coordinate b C t
  H.trans (({
    toFun := fun x ↦ g • x
    invFun := fun x ↦ g⁻¹ • x
    left_inv := fun x ↦ inv_smul_smul g x
    right_inv := fun x ↦ smul_inv_smul g x
    continuous_toFun := hC g
    continuous_invFun := hC g⁻¹ } : C ≃ₜ C).trans H.symm)

set_option backward.isDefEq.respectTransparency false in
theorem hga_toFibre_deck (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (g : b4b_Group) (x : hg2_H1 ℤ b4b_root) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    hg9_toFibre F V hV t (hg2_H1act ℤ b4b_root g x) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ g))
        (hg9_toFibre F V hV t x) := by
  intro F
  let H := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  have hd := hg8_H1map_deck U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL g x
  change b6m_H1Equiv H.symm (hg8_H1map F (hg2_H1act ℤ b4b_root g x)) =
    homologyMap ℤ 1 (TopCat.ofHom (b6m_deck mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ g))
      (b6m_H1Equiv H.symm (hg8_H1map F x))
  rw [hd]
  have hsq : TopCat.ofHom (⟨fun c : C ↦ g • c, hC g⟩ : C(C, C)) ≫
      TopCat.ofHom (⟨H.symm, H.symm.continuous⟩ : C(C, b6m_Fibre mr_base C ⟨t.val, hV t.property⟩)) =
      TopCat.ofHom (⟨H.symm, H.symm.continuous⟩ : C(C, b6m_Fibre mr_base C ⟨t.val, hV t.property⟩)) ≫
        TopCat.ofHom (b6m_deck mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ g) := by
    ext c
    rfl
  have hcomp := congrArg (fun φ ↦ homologyMap ℤ 1 φ (hg8_H1map F x)) hsq
  simp only [homologyMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  exact hcomp

set_option backward.isDefEq.respectTransparency false in
theorem hga_cellIntersection_deck (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
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
    (hQ : b3_IsIntersectionForm ℂ Q) (g : b4b_Group) (a b : hg2_H1 ℤ b4b_root) :
    let F := hg8_liftMap U π hπ y₀ hy₀ u₀ b4b_root γ hγ hroot C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
    hga_cellIntersection F V hV t P Q (hg2_H1act ℤ b4b_root g a) (hg2_H1act ℤ b4b_root g b) =
      hga_cellIntersection F V hV t P Q a b := by
  intro F
  let T := b63l_parameterFibre mr_base C V hV t
  let H : T ≃ₜ C := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  letI : PathConnectedSpace C := hga_lift_pathConnected U π hπ y₀ hy₀ u₀ γ hγ hroot
    C hC f hf hfinv hftr hstab ι hι hιr hfι hιG L hL
  letI : PathConnectedSpace T := H.symm.pathConnectedSpace
  letI : CompactSpace T := H.symm.compactSpace
  letI : T2Space T := H.symm.t2Space
  let k := b63d_projection mr_base C f V hV t
  let e := hga_deckHomeomorph mr_base b4b_Group C hC ⟨t.val, hV t.property⟩ g
  have he : ∀ x : T, k (e x) = k x := by
    intro x
    change b6t_sphere mr_base t.val (f (g • x.val.2)) =
      b6t_sphere mr_base x.val.1.val (f x.val.2)
    rw [hfinv, x.property]
  let τ : hg2_Tri b4b_Group 13 := Sum.inl (0, 1)
  have hproj := hga_firstLift_projection f (L τ) (hL τ).1 V hV t
  have hnc : ∃ p q : T, k p ≠ k q := by
    apply hga_nonconstant_of_plane_lift
      ((⟨H.symm, H.symm.continuous⟩ : C(C, T)).comp
        (hga_wedgeLift (L τ) (hg3_waist 0) (hg5_markRe 0))) k (-37 / 3)
    filter_upwards [hproj] with z hz
    change b63d_projection mr_base C f V hV t
      (H.symm (hga_wedgeLift (L τ) (hg3_waist 0) (hg5_markRe 0) z)) = _
    simpa only [sub_eq_add_neg, neg_div] using hz
  have h := b6m_intersection_same_filling k k hk hk hnc e he P hP P hP Q hQ Q hQ
    (hg9_toFibre F V hV t a) (hg9_toFibre F V hV t b)
  change Q (P (hg9_toFibre F V hV t (hg2_H1act ℤ b4b_root g a)))
    (P (hg9_toFibre F V hV t (hg2_H1act ℤ b4b_root g b))) = _
  rw [hga_toFibre_deck U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL V hV t g a,
    hga_toFibre_deck U π hπ y₀ hy₀ u₀ γ hγ hroot C hC f hf hfinv hftr hstab
    ι hι hιr hfι hιG L hL V hV t g b]
  exact h

#print axioms hga_cellIntersection_deck

#print axioms hga_toFibre_deck

#print axioms hga_deckHomeomorph
#print axioms hga_nonconstant_of_plane_lift
end HodgeLean.Foundations.Program
