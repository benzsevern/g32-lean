import HodgeLean.Foundations.Program.SchoenCycleBranchAdicKernel
import HodgeLean.Foundations.Program.SchoenCycleCollisionAdicBranch
import HodgeLean.Foundations.Program.SchoenCycleInsertionAdicKernel

/-! # Principality of the actual branch ideal in the downstairs adic stalk -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained branch-image ideal becomes principal in the actual downstairs
adic stalk, with a generator whose pullback is exactly the product of parameters.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_total_collision_branch_adic_principal
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
    let x := Point.map (s2c_branchInsertion Z n a) y
    let R := (g3_power Z (n + 1)).left.presheaf.stalk x.underlying
    let D := B.left.presheaf.stalk (γ.left x.underlying)
    ∃ c : AdicCompletion (IsLocalRing.maximalIdeal D) D,
      (((s2c_branchIdeal Z B n γ a).ideal U).map
        (B.left.presheaf.germ U.1 (γ.left x.underlying) hu).hom).map
          (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D)) = Ideal.span {c} ∧
      s2e_adic_stalkMap γ.left x.underlying c =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R
          (∏ i, s2e_curvePowerParameter Z (n + 1) x i) := by
  let q := s2c_branchInsertion Z n a
  let x := Point.map q y
  obtain ⟨c, hc, hi⟩ := s2e_total_collision_adic_marked_ideal
    Z B (n + 1) γ hγ hquot x a hx
  refine ⟨c, ?_, hc⟩
  refine (s2e_total_collision_branch_adic_stalk_kernel Z B n γ hγ hquot y a hx U hu).symm.trans ?_
  have hcomp : s2e_adic_stalkMap (q ≫ γ).left y.underlying =
      (s2e_adic_stalkMap q.left y.underlying).comp
        (s2e_adic_stalkMap γ.left (q.left y.underlying)) := by
    apply RingHom.ext
    intro z
    exact s2e_adic_stalkMap_comp q.left γ.left y.underlying z
  rw [hcomp, ← RingHom.comap_ker, s2e_branchInsertion_adic_stalk_kernel]
  exact hi 0

#print axioms s2e_total_collision_branch_adic_principal
end HodgeLean.Foundations.Program
