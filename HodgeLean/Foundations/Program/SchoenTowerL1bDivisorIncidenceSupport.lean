import HodgeLean.Foundations.Program.SchoenTowerL1aPreProofs

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The ideal of an actual complex point of a separated scheme has singleton support. -/
theorem s2v_l1b_divisor_complex_point_kernel_support
    (Z : Over (Spec ↧ℂ)) [IsSeparated Z.hom] (b : ComplexPoint Z) :
    (b.left.ker.support : Set Z.left) = {b.underlying} := by
  letI : IsClosedImmersion (b.left ≫ Z.hom) := by
    rw [Over.w b]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion b.left := IsClosedImmersion.of_comp b.left Z.hom
  have hrange : Set.range b.left = {b.underlying} := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg b.left (Subsingleton.elim (α := Spec ↧ℂ) w (closedPoint ℂ)))
    · rintro z rfl
      exact ⟨closedPoint ℂ, rfl⟩
  have hc : IsClosed ({b.underlying} : Set Z.left) := by
    rw [← hrange]
    exact b.left.isClosedMap.isClosed_range
  rw [Scheme.Hom.support_ker, hrange, hc.closure_eq]

/-- Membership in a product ideal support means membership in at least one factor support. -/
theorem s2v_l1b_divisor_product_support_iff
    (X : Scheme) {J : Type*} [Fintype J] (I : J → X.IdealSheafData) (x : X) :
    x ∈ (∏ j, I j).support ↔ ∃ j, x ∈ (I j).support := by
  classical
  have H (s : Finset J) : x ∈ (∏ j ∈ s, I j).support ↔ ∃ j ∈ s, x ∈ (I j).support := by
    induction s using Finset.induction_on with
    | empty =>
      change (False ↔ ∃ j ∈ (∅ : Finset J), x ∈ (I j).support)
      exact ⟨False.elim, fun ⟨j, hj, _⟩ => Finset.notMem_empty j hj⟩
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Scheme.IdealSheafData.support_mul]
      change (x ∈ (I j).support ∨ x ∈ (∏ k ∈ s, I k).support) ↔ _
      rw [ih]
      simp only [Finset.exists_mem_insert]
  simpa only [Finset.mem_univ, true_and] using H Finset.univ

/-- Incidence support at an arbitrary ordered point is detected by equality of one coordinate with the marked point. -/
theorem s2v_l1b_divisor_incidence_support_coordinate
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (b : ComplexPoint Z) (y : (g3_power Z (h + 1)).left) :
    γ.left y ∈ (s2c_branchIdeal Z B h γ b).support ↔
      ∃ i : Fin (h + 1), (g3_proj Z (h + 1) i).left y = b.underlying := by
  have H : y ∈ ((s2c_branchIdeal Z B h γ b).comap γ.left).support ↔
      ∃ i : Fin (h + 1), y ∈ ((b.left.ker).comap (g3_proj Z (h + 1) i).left).support := by
    rw [s2v_l1a_pre_local_to_global_aux Z B hdimZ h γ hγsurj hγinv hγ b]
    exact s2v_l1b_divisor_product_support_iff _ _ y
  rw [Scheme.IdealSheafData.support_comap] at H
  refine H.trans (exists_congr fun i => ?_)
  rw [Scheme.IdealSheafData.support_comap]
  change (g3_proj Z (h + 1) i).left y ∈ (b.left.ker.support : Set Z.left) ↔ _
  rw [s2v_l1b_divisor_complex_point_kernel_support, Set.mem_singleton_iff]

/-- A local equation has a unit germ exactly outside the support of its ideal sheaf. -/
theorem s2v_l1b_divisor_generator_unit_iff
    (X : Scheme) (I : X.IdealSheafData) (U : X.affineOpens)
    (g : Γ(X, U.1)) (hg : I.ideal U = Ideal.span {g})
    (x : X) (hx : x ∈ U.1) :
    IsUnit (X.presheaf.germ U.1 x hx g) ↔ x ∉ I.support := by
  rw [I.mem_support_iff_of_mem hx, hg, X.zeroLocus_span, X.zeroLocus_singleton]
  simpa only [Set.mem_compl_iff, not_not, SetLike.mem_coe] using (X.mem_basicOpen g x hx).symm

end HodgeLean.Foundations.Program
