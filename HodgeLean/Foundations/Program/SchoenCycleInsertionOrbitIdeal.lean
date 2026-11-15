import HodgeLean.Foundations.Program.SchoenCyclePermutedInsertionParameters
import HodgeLean.Foundations.Program.SchoenCycleFiniteIdealStalks
import HodgeLean.Foundations.Program.SchoenCycleBranchImagePoints
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The actual union of permuted marked insertion images -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The ideal of the union of actual permuted marked insertion images.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15. -/
def s2e_insertionOrbitIdeal (Z : Over (Spec ↧ℂ)) (n : ℕ) (a : ComplexPoint Z) :
    (g3_power Z (n + 1)).left.IdealSheafData :=
  ⨅ σ : Equiv.Perm (Fin (n + 1)),
    (s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ).left.ker

/-- Permuting the factors preserves the actual union ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15. -/
theorem s2e_insertionOrbitIdeal_map_permute
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (a : ComplexPoint Z)
    (u : Equiv.Perm (Fin (n + 1))) :
    (s2e_insertionOrbitIdeal Z n a).map (s2_permute Z (n + 1) u).left =
      s2e_insertionOrbitIdeal Z n a := by
  unfold s2e_insertionOrbitIdeal
  rw [(Scheme.IdealSheafData.map_gc (s2_permute Z (n + 1) u).left).u_iInf]
  simp_rw [Scheme.IdealSheafData.map_ker]
  calc
    (⨅ σ : Equiv.Perm (Fin (n + 1)),
      ((s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ).left ≫
        (s2_permute Z (n + 1) u).left).ker) =
      ⨅ σ : Equiv.Perm (Fin (n + 1)),
        (s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) (u * σ)).left.ker := by
      apply iInf_congr
      intro σ
      congr 1
      change ((s2c_branchInsertion Z n a).left ≫ (s2_permute Z (n + 1) σ).left) ≫
        (s2_permute Z (n + 1) u).left = _
      rw [Category.assoc]
      exact congrArg (fun v : g3_power Z (n + 1) ⟶ g3_power Z (n + 1) =>
        (s2c_branchInsertion Z n a).left ≫ v.left)
        (s2e_step1_permute_mul Z (n + 1) u σ).symm
    _ = _ := by
      let F := fun σ : Equiv.Perm (Fin (n + 1)) =>
        (s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ).left.ker
      change (⨅ σ, F (u * σ)) = ⨅ σ, F σ
      apply le_antisymm
      · apply le_iInf
        intro σ
        have h := iInf_le (fun τ => F (u * τ)) (u⁻¹ * σ)
        simpa only [mul_inv_cancel_left] using h
      · apply le_iInf
        intro σ
        exact iInf_le F (u * σ)

/-- The actual marked-coordinate product belongs to the ideal of the union of all permuted insertion images in the tuple stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_marked_product_mem_insertionOrbitIdeal_stalk
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z (n + 1)))
    (S : Finset (Fin (n + 1)))
    (hS : ∀ i, i ∈ S ↔ Point.map (g3_proj Z (n + 1) i) x = a)
    (U : (g3_power Z (n + 1)).left.affineOpens) (hxU : x.underlying ∈ U.1) :
    (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) ∈
      Ideal.map ((g3_power Z (n + 1)).left.presheaf.germ U.1 x.underlying hxU).hom
        ((s2e_insertionOrbitIdeal Z n a).ideal U) := by
  rw [s2e_insertionOrbitIdeal, Scheme.IdealSheafData.ideal_iInf, iInf_apply,
    s2e_affine_stalk_map_finite_iInf, Ideal.mem_iInf]
  intro σ
  let u := s2_permute Z (n + 1) σ
  letI : IsIso u := s2e_step1_action_isIso (g3_power Z (n + 1))
    (Equiv.Perm (Fin (n + 1))) (s2_permute Z (n + 1))
    (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) σ
  letI : IsClosedImmersion (s2c_branchInsertion Z n a).left :=
    s2e_branchInsertion_isClosedImmersion Z n a
  let f := s2c_branchInsertion Z n a ≫ u
  letI : IsFinite f.left := by
    change IsFinite ((s2c_branchInsertion Z n a).left ≫ u.left)
    infer_instance
  by_cases hx : x.underlying ∈ f.left.ker.support
  · have hrange : x.underlying ∈ Set.range f.left := by
      change x.underlying ∈ (f.left.ker.support : Set _) at hx
      rw [Scheme.Hom.support_ker, f.left.isClosedMap.isClosed_range.closure_eq] at hx
      exact hx
    obtain ⟨y, hy⟩ := s2e_complexPoint_lift_of_mem_range f x hrange
    have hcoord : Point.map (g3_proj Z (n + 1) (σ 0)) (Point.map f y) = a := by
      change y ≫ ((s2c_branchInsertion Z n a ≫ u) ≫ g3_proj Z (n + 1) (σ 0)) = a
      rw [Category.assoc, show u ≫ g3_proj Z (n + 1) (σ 0) =
        g3_proj Z (n + 1) 0 by
          simpa only [u, s2_permute, Equiv.symm_apply_apply] using
            (s2_check_lift_proj (n + 1)
              (fun i => g3_proj Z (n + 1) (σ.symm i)) (σ 0))]
      rw [show s2c_branchInsertion Z n a ≫ g3_proj Z (n + 1) 0 =
        CartesianMonoidalCategory.toUnit _ ≫ a from s2_check_lift_proj _ _ 0,
        ← Category.assoc]
      have hu : y ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
        (SemiCartesianMonoidalCategory.isTerminalTensorUnit).hom_ext _ _
      rw [hu, Category.id_comp]
    rw [hy] at hcoord
    have hi := (hS (σ 0)).mpr hcoord
    rcases hy with rfl
    exact s2e_permutedInsertion_product_mem_image_stalk Z n a σ y S hi U hxU
  · rw [s2e_ideal_stalk_eq_top_off_support f.left.ker U x.underlying hxU hx]
    exact Submodule.mem_top

/-- Pullback into the actual insertion union ideal forces membership in the actual retained branch ideal downstairs.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_branchIdeal_mem_of_pullback_mem_insertionOrbitIdeal
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (a : ComplexPoint Z) (U : B.left.affineOpens) (c : Γ(B.left, U.1))
    (hc : (γ.left.app U.1).hom c ∈ (s2e_insertionOrbitIdeal Z n a).ideal
      ⟨γ.left ⁻¹ᵁ U.1, U.2.preimage γ.left⟩) :
    c ∈ (s2c_branchIdeal Z B n γ a).ideal U := by
  have hle : s2e_insertionOrbitIdeal Z n a ≤ (s2c_branchInsertion Z n a).left.ker := by
    have h := iInf_le (fun σ : Equiv.Perm (Fin (n + 1)) =>
      (s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ).left.ker) 1
    simpa only [s2e_insertionOrbitIdeal, s2e_step1_permute_one, Category.comp_id] using h
  have hk := (s2c_branchInsertion Z n a).left.ideal_ker_le
    ⟨γ.left ⁻¹ᵁ U.1, U.2.preimage γ.left⟩ (hle _ hc)
  rw [s2e_branchIdeal_affine_kernel]
  change ((s2c_branchInsertion Z n a).left ≫ γ.left).app U.1 c = 0
  rw [Scheme.Hom.comp_app]
  exact hk

end HodgeLean.Foundations.Program
