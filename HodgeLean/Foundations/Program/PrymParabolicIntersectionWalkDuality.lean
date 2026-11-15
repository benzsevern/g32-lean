import HodgeLean.Foundations.Program.PrymParabolicIntersectionWalkCrossing
import HodgeLean.Foundations.Program.PrymParabolicIntersectionDuality

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

/-! ## Coefficients of the cyclic walks of a cocycle and of a cycle -/

section Coef

open Classical

variable {G : Type} [Group G] [Fintype G] (g : Fin 13 → G)

/-- For a cellular cocycle `α`, the coefficients of the cyclic dual walks
`W(τ_out ε₁) · ε₁ · W(τ_in ε₁)⁻¹` weighted by `α` add up to `α`. -/
theorem hga_cocycle_coef (α : hg2_Edge G 13 → ℤ) (hα : hg2_delta1 ℤ ℤ g α = 0)
    (W : hg2_Tri G 13 → List (hg2_Edge G 13 × Bool)) (ε : hg2_Edge G 13) :
    ∑ ε₁, α ε₁ * hga_coef (W (hga_triOut g ε₁) ++ [(ε₁, true)] ++ hga_rev (W (hga_triIn ε₁))) ε =
      α ε := by
  simp only [hga_coef_append, hga_coef_rev, hga_coef_single]
  have hb := hga_cocycle_balance g α hα (fun τ ↦ hga_coef (W τ) ε)
  simp only [smul_eq_mul] at hb
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hb]
  have hδ : ∑ x, α x * (if x = ε then 1 else 0) = α ε := by
    simp [mul_ite, Finset.sum_ite_eq']
  rw [hδ]
  ring

/-- For a cellular cycle `z`, the coefficients of the cyclic edge walks
`W(src ε₂) · ε₂ · W(tgt ε₂)⁻¹` weighted by `z` add up to `z`. -/
theorem hga_cycle_coef (z : hg2_Edge G 13 →₀ ℤ) (hz : hg2_bd1 ℤ g z = 0)
    (W : hg2_Vert g → List (hg2_Edge G 13 × Bool)) (ε : hg2_Edge G 13) :
    ∑ ε₂, z ε₂ * hga_coef (W (hg2_src g ε₂) ++ [(ε₂, true)] ++ hga_rev (W (hg2_tgt g ε₂))) ε =
      z ε := by
  simp only [hga_coef_append, hga_coef_rev, hga_coef_single]
  have hb := hga_cycle_balance z hz (fun v ↦ hga_coef (W v) ε)
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hb]
  have hδ : ∑ x, z x * (if x = ε then 1 else 0) = z ε := by
    simp [mul_ite, Finset.sum_ite_eq']
  rw [hδ]
  ring

end Coef

/-! ## Intersection numbers of the classes of cyclic walks -/

section Classes

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

variable {G : Type} [Group G] [Fintype G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
  [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T] [T2Space T]
variable {D : hg8_DeltaMap g T}
variable (j : b6m_H1 T →ₗ[ℤ] b6m_chainQuotient (TopCat.toSSet.obj (TopCat.of T)))
  (hj : ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
    j (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z) =
      b6m_chainQuotientMap _ z.1)

include hj in
theorem hga_dWalk_class (hW : hga_WinFacts D) (τ₀ : hg2_Tri G 13)
    (u : List (hg2_Edge G 13 × Bool)) (hu : hga_DChain g τ₀ u τ₀) (hun : 0 < u.length)
    (v₀ : hg2_Vert g) (w : List (hg2_Edge G 13 × Bool)) (hw : hga_PChain g v₀ w v₀)
    (hwn : 0 < w.length) :
    ∃ x, j x = b6m_chainQuotientMap _ (hga_dWalkChain D u) := by
  obtain ⟨A, -, hA, -⟩ := hga_walk_crossing hW τ₀ u hu hun v₀ w hw hwn
  exact ⟨_, (hga_loopClass_chain A.smoothLoop j hj).trans hA⟩

include hj in
theorem hga_pWalk_class (hW : hga_WinFacts D) (τ₀ : hg2_Tri G 13)
    (u : List (hg2_Edge G 13 × Bool)) (hu : hga_DChain g τ₀ u τ₀) (hun : 0 < u.length)
    (v₀ : hg2_Vert g) (w : List (hg2_Edge G 13 × Bool)) (hw : hga_PChain g v₀ w v₀)
    (hwn : 0 < w.length) :
    ∃ y, j y = b6m_chainQuotientMap _ (hga_pWalkChain D w) := by
  obtain ⟨-, B, -, hB, -⟩ := hga_walk_crossing hW τ₀ u hu hun v₀ w hw hwn
  exact ⟨_, (hga_loopClass_chain B.smoothLoop j hj).trans hB⟩

include hj in
/-- **Intersection numbers of walk classes.** The intersection form on the classes of a cyclic
dual walk `u` and a cyclic edge walk `w` is `Σ_ε c_u(ε) c_w(ε)`. -/
theorem hga_walk_intersection (hW : hga_WinFacts D) (hjinj : Function.Injective j)
    (P : b6m_H1 T →ₗ[ℤ] b3_periodLattice ℂ T)
    (hP : ∀ γ : b3_SmoothLoop ℂ T, P (b6m_loopClass T γ) = b3_latticePeriod ℂ T γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ T)) (hQ : b3_IsIntersectionForm ℂ Q)
    (τ₀ : hg2_Tri G 13)
    (u : List (hg2_Edge G 13 × Bool)) (hu : hga_DChain g τ₀ u τ₀) (hun : 0 < u.length)
    (v₀ : hg2_Vert g) (w : List (hg2_Edge G 13 × Bool)) (hw : hga_PChain g v₀ w v₀)
    (hwn : 0 < w.length) (x y : b6m_H1 T)
    (hx : j x = b6m_chainQuotientMap _ (hga_dWalkChain D u))
    (hy : j y = b6m_chainQuotientMap _ (hga_pWalkChain D w)) :
    Q (P x) (P y) = ∑ ε, hga_coef u ε * hga_coef w ε := by
  obtain ⟨A, B, hA, hB, htr, hint⟩ := hga_walk_crossing hW τ₀ u hu hun v₀ w hw hwn
  have ex : x = b6m_loopClass T A.smoothLoop :=
    hjinj (hx.trans ((hga_loopClass_chain A.smoothLoop j hj).trans hA).symm)
  have ey : y = b6m_loopClass T B.smoothLoop :=
    hjinj (hy.trans ((hga_loopClass_chain B.smoothLoop j hj).trans hB).symm)
  rw [ex, ey, hP, hP, hQ _ _ htr, hint]

end Classes

/-! ## Duality for the barycentric dual cycle -/

section Duality

open Classical CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T] [T2Space T]

/-- **Duality for the barycentric dual cycle.** For a realization of `X̃(b4b_root)` with the window
facts whose cellular `H₁` map is onto, the dual cycle of a singular `1`-cocycle `φ` pairs with
every singular `1`-cycle `z` as `φ z` under the intersection form.
Source: Hatcher, *Algebraic Topology*, §3.3 (dual cells and Poincaré duality); Farkas–Kra, III.1. -/
theorem hga_duality_of_winFacts (D : hg8_DeltaMap b4b_root T) (hW : hga_WinFacts D)
    (hsurj : Function.Surjective (hg8_H1map D))
    (P : b6m_H1 T →ₗ[ℤ] b3_periodLattice ℂ T)
    (hP : ∀ γ : b3_SmoothLoop ℂ T, P (b6m_loopClass T γ) = b3_latticePeriod ℂ T γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ T)) (hQ : b3_IsIntersectionForm ℂ Q)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ ∘ₗ Simplicial.boundary ℤ 1 = 0)
    (z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom) :
    Q (P (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
        (hga_dual_fundCycle D φ hφ)))
      (P (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z)) = φ z.1 := by
  obtain ⟨j, hjinj, hj⟩ := b6m_homology_chain_embedding T
  let α : hg2_Edge b4b_Group 13 → ℤ := fun ε ↦ φ (hg5_chain1 D.edge (Finsupp.single ε 1))
  have hα : hg2_delta1 ℤ ℤ b4b_root α = 0 := hga_restriction_cocycle D φ hφ
  let τ₀ : hg2_Tri b4b_Group 13 := Sum.inl (0, 1)
  let v₀ : hg2_Vert b4b_root := Sum.inl 1
  have hdc : ∀ τ, ∃ L, hga_DChain b4b_root τ₀ L τ :=
    hga_dual_connected b4b_root b63d_root_subgroup
  have hpc : ∀ v, ∃ L, hga_PChain b4b_root v₀ L v :=
    hga_primal_connected b4b_root b63d_root_product b63d_root_subgroup
  choose W hWc using hdc
  choose V hVc using hpc
  let u : hg2_Edge b4b_Group 13 → List (hg2_Edge b4b_Group 13 × Bool) := fun ε ↦
    W (hga_triOut b4b_root ε) ++ [(ε, true)] ++ hga_rev (W (hga_triIn ε))
  let w : hg2_Edge b4b_Group 13 → List (hg2_Edge b4b_Group 13 × Bool) := fun ε ↦
    V (hg2_src b4b_root ε) ++ [(ε, true)] ++ hga_rev (V (hg2_tgt b4b_root ε))
  have hu : ∀ ε, hga_DChain b4b_root τ₀ (u ε) τ₀ := fun ε ↦
    hga_DChain_append b4b_root (hga_DChain_snoc b4b_root (hWc _) (ε, true) rfl)
      (hga_DChain_rev b4b_root (hWc (hga_triIn ε)))
  have hw : ∀ ε, hga_PChain b4b_root v₀ (w ε) v₀ := fun ε ↦
    hga_PChain_append b4b_root (hga_PChain_snoc b4b_root (hVc _) (ε, true) rfl)
      (hga_PChain_rev b4b_root (hVc (hg2_tgt b4b_root ε)))
  have hun : ∀ ε, 0 < (u ε).length := fun ε ↦ by simp [u]
  have hwn : ∀ ε, 0 < (w ε).length := fun ε ↦ by simp [w]
  let e₀ : hg2_Edge b4b_Group 13 := Sum.inl (0, 1)
  have hxu : ∀ ε, ∃ x, j x = b6m_chainQuotientMap _ (hga_dWalkChain D (u ε)) := fun ε ↦
    hga_dWalk_class j hj hW τ₀ (u ε) (hu ε) (hun ε) v₀ (w e₀) (hw e₀) (hwn e₀)
  have hyw : ∀ ε, ∃ y, j y = b6m_chainQuotientMap _ (hga_pWalkChain D (w ε)) := fun ε ↦
    hga_pWalk_class j hj hW τ₀ (u e₀) (hu e₀) (hun e₀) v₀ (w ε) (hw ε) (hwn ε)
  choose x hx using hxu
  choose y hy using hyw
  -- the class of the dual cycle
  have hd : ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
      (hga_dual_fundCycle D φ hφ) = ∑ ε₁, α ε₁ • x ε₁ := by
    apply hjinj
    rw [hj, map_sum]
    simp only [map_zsmul, hx]
    change b6m_chainQuotientMap _ (hga_dualChain D α hg2_orient) = _
    rw [hga_dualChain_decomp D α hα W, map_sum]
    simp only [map_zsmul]
    rfl
  -- the class of `z`, through a cellular cycle
  obtain ⟨c, hc⟩ := hsurj (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z)
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hz' : hg2_bd1 ℤ b4b_root z'.1 = 0 := LinearMap.mem_ker.mp z'.2
  have hcz : ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z =
      ∑ ε₂, z'.1 ε₂ • y ε₂ := by
    apply hjinj
    rw [← hc, map_sum]
    simp only [map_zsmul, hy]
    refine (hj (hg8_cycle1 D z')).trans ?_
    change b6m_chainQuotientMap _ (hg5_chain1 D.edge z'.1) = _
    rw [hga_cycle_decomp D z'.1 hz' V, map_sum]
    simp only [map_zsmul]
    rfl
  -- the value of `φ` on `z`
  have hφz : φ z.1 = ∑ ε, z'.1 ε * α ε := by
    have h1 : b6m_chainQuotientMap _ z.1 = b6m_chainQuotientMap _ (hg5_chain1 D.edge z'.1) := by
      rw [← hj z, ← hc]
      exact hj (hg8_cycle1 D z')
    obtain ⟨b, hb⟩ := (QuotientAddGroup.eq).mp h1
    have h2 := LinearMap.congr_fun hφ b
    change φ (Simplicial.boundary ℤ 1 b) = 0 at h2
    rw [hb] at h2
    rw [map_add] at h2
    erw [map_neg] at h2
    rw [neg_add_eq_zero] at h2
    rw [h2, hga_cochain_chain1 D φ z'.1]
    exact Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)
  have hQP : ∀ ε₁ ε₂, Q (P (x ε₁)) (P (y ε₂)) =
      ∑ ε, hga_coef (u ε₁) ε * hga_coef (w ε₂) ε := fun ε₁ ε₂ ↦
    hga_walk_intersection j hj hW hjinj P hP Q hQ τ₀ (u ε₁) (hu ε₁) (hun ε₁) v₀ (w ε₂) (hw ε₂)
      (hwn ε₂) (x ε₁) (y ε₂) (hx ε₁) (hy ε₂)
  rw [hd, hcz, hφz]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, hQP]
  have hR : ∑ ε, z'.1 ε * α ε = ∑ ε, (∑ ε₂, z'.1 ε₂ * hga_coef (w ε₂) ε) *
      (∑ ε₁, α ε₁ * hga_coef (u ε₁) ε) := Finset.sum_congr rfl fun ε _ ↦ by
    rw [hga_cocycle_coef b4b_root α hα W ε, hga_cycle_coef b4b_root z'.1 hz' V ε]
  rw [hR]
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ ε₂, ∑ ε, ∑ ε₁, z'.1 ε₂ * (α ε₁ * (hga_coef (u ε₁) ε * hga_coef (w ε₂) ε)) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ ε, ∑ ε₂, ∑ ε₁, z'.1 ε₂ * (α ε₁ * (hga_coef (u ε₁) ε * hga_coef (w ε₂) ε)) :=
        Finset.sum_comm
    _ = ∑ ε, ∑ ε₁, ∑ ε₂, z'.1 ε₂ * (α ε₁ * (hga_coef (u ε₁) ε * hga_coef (w ε₂) ε)) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
        Finset.sum_congr rfl fun _ _ ↦ by ring

end Duality

end HodgeLean.Foundations.Program
