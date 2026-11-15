import HodgeLean.Foundations.Program.SchoenCycleBranchCompositeStalk
import HodgeLean.Foundations.Program.SchoenCycleBranchCollisionFiber
import HodgeLean.Foundations.Program.SchoenCycleSingletonAdicKernel
import HodgeLean.Foundations.Program.SchoenCycleQuotientNoetherian
import HodgeLean.Foundations.Program.SchoenCycleBranchAffineImage
import HodgeLean.Foundations.Program.SchoenCycleAdicIdealKernel
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The actual affine branch image under adic extension -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual affine branch-image ideal extends to the kernel of the
canonical adic ring map induced by the branch composite.
Source: Hartshorne, Algebraic Geometry, II.5; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapter 10, Propositions 10.12–10.13. -/
theorem s2e_branchIdeal_affine_adic_kernel
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] [IsLocallyNoetherian B.left]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (a : ComplexPoint Z) (U : B.left.affineOpens) (I : Ideal Γ(B.left, U.1)) :
    let f := ((s2c_branchInsertion Z n a ≫ γ).left.app U.1).hom
    RingHom.ker (s2e_adic_ring_map I (I.map f) f le_rfl) =
      ((s2c_branchIdeal Z B n γ a).ideal U).map
        (algebraMap Γ(B.left, U.1) (AdicCompletion I Γ(B.left, U.1))) := by
  let q := s2c_branchInsertion Z n a
  letI : IsClosedImmersion q.left := s2e_branchInsertion_isClosedImmersion Z n a
  let h := (q ≫ γ).left
  letI : IsFinite h := by
    change IsFinite (q.left ≫ γ.left)
    infer_instance
  let R := Γ(B.left, U.1)
  let S := Γ((g3_power Z n).left, h ⁻¹ᵁ U.1)
  letI : Algebra R S := (h.app U.1).hom.toAlgebra
  letI : Module.Finite R S := h.finite_app U.1 U.2
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  rw [s2e_branchIdeal_affine_kernel]
  exact s2e_adic_algebraMap_kernel (S := S) I

#print axioms s2e_branchIdeal_affine_adic_kernel
/-- At an actual total collision, the kernel of the branch composite's
adic stalk map is the extension of the retained branch-image ideal through
the actual affine germ.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_total_collision_branch_adic_stalk_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (y : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z (n + 1) i)
      (Point.map (s2c_branchInsertion Z n a) y) = a)
    (U : B.left.affineOpens)
    (hu : (s2c_branchInsertion Z n a ≫ γ).left y.underlying ∈ U.1) :
    let f := (s2c_branchInsertion Z n a ≫ γ).left
    let D := B.left.presheaf.stalk (f y.underlying)
    RingHom.ker (s2e_adic_stalkMap f y.underlying) =
      (((s2c_branchIdeal Z B n γ a).ideal U).map
        (B.left.presheaf.germ U.1 (f y.underlying) hu).hom).map
          (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D)) := by
  let q := s2c_branchInsertion Z n a
  let f := (q ≫ γ).left
  letI : IsClosedImmersion q.left := s2e_branchInsertion_isClosedImmersion Z n a
  letI : IsFinite f := by
    change IsFinite (q.left ≫ γ.left)
    infer_instance
  letI : IsLocallyNoetherian (g3_power Z (n + 1)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z (n + 1)).hom
  letI := s2e_quotient_isLocallyNoetherian (g3_power Z (n + 1)) B (Equiv.Perm (Fin (n + 1)))
    (s2_permute Z (n + 1)) (s2e_step1_permute_one Z (n + 1))
    (s2e_step1_permute_mul Z (n + 1)) γ hγ hquot
  letI : IsLocallyNoetherian (g3_power Z n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z n).hom
  letI : IsClosedImmersion y.left :=
    isClosedImmersion_of_comp_eq_id (g3_power Z n).hom y.left (Over.w y)
  have hcy : IsClosed ({y.underlying} : Set (g3_power Z n).left) := by
    change IsClosed {y.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using y.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({f y.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using f.isClosedMap {y.underlying} hcy
  have hf := s2e_total_collision_branch_scheme_fiber Z B n γ hγ hquot y a hx
  dsimp only
  rw [s2e_branchIdeal_affine_kernel]
  exact s2e_singleton_fiber_adic_stalk_kernel_ideal f y.underlying hcb hf U.1 U.2 hu

#print axioms s2e_total_collision_branch_adic_stalk_kernel
/-- At a total collision, the retained algebraic branch-image stalk ideal
is exactly the contraction of the marked parameter ideal along the actual
quotient stalk map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_total_collision_branch_stalk_contraction
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (y : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z (n + 1) i)
      (Point.map (s2c_branchInsertion Z n a) y) = a)
    (U : B.left.affineOpens)
    (hu : (s2c_branchInsertion Z n a ≫ γ).left y.underlying ∈ U.1) :
    (((s2c_branchIdeal Z B n γ a).ideal U).map
      (B.left.presheaf.germ U.1 ((s2c_branchInsertion Z n a ≫ γ).left y.underlying) hu).hom) =
    (Ideal.span {(s2e_curvePowerParameter Z (n + 1)
      (Point.map (s2c_branchInsertion Z n a) y) 0)}).comap
        (γ.left.stalkMap ((s2c_branchInsertion Z n a).left y.underlying)).hom := by
  let q := s2c_branchInsertion Z n a
  let f := (q ≫ γ).left
  letI : IsClosedImmersion q.left := s2e_branchInsertion_isClosedImmersion Z n a
  letI : IsFinite f := by
    change IsFinite (q.left ≫ γ.left)
    infer_instance
  letI : IsLocallyNoetherian (g3_power Z (n + 1)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z (n + 1)).hom
  letI := s2e_quotient_isLocallyNoetherian (g3_power Z (n + 1)) B (Equiv.Perm (Fin (n + 1)))
    (s2_permute Z (n + 1)) (s2e_step1_permute_one Z (n + 1))
    (s2e_step1_permute_mul Z (n + 1)) γ hγ hquot
  letI : IsLocallyNoetherian (g3_power Z n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z n).hom
  letI : IsClosedImmersion y.left :=
    isClosedImmersion_of_comp_eq_id (g3_power Z n).hom y.left (Over.w y)
  have hcy : IsClosed ({y.underlying} : Set (g3_power Z n).left) := by
    change IsClosed {y.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using y.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({f y.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using f.isClosedMap {y.underlying} hcy
  have hf := s2e_total_collision_branch_scheme_fiber Z B n γ hγ hquot y a hx
  rw [s2e_branchIdeal_affine_kernel]
  rw [← s2e_singleton_fiber_stalk_kernel f y.underlying hcb hf U.1 U.2 hu]
  exact s2e_branch_composite_stalk_kernel Z B n γ a y

#print axioms s2e_total_collision_branch_stalk_contraction
end HodgeLean.Foundations.Program
