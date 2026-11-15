import HodgeLean.Foundations.Program.SchoenCycleBranchOffSupport
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepRefinement
import HodgeLean.Foundations.Program.SchoenCycleC11DegreeHelpers

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- All marked branches absent from the actual symmetric tuple have unit
ideals on one affine neighbourhood inside any prescribed initial open. -/
theorem s2e_c1_absent_branches_unit_neighbourhood
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (q : ℕ) (γ : g3_power Z (q + 1) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (q + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (q + 1) ⟶ T),
      (∀ σ, s2_permute Z (q + 1) σ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    {I : Type} [Fintype I] (marks : I → ComplexPoint Z)
    (x : ComplexPoint (g3_power Z (q + 1))) (U : B.left.Opens)
    (hx : γ.left x.underlying ∈ U) :
    ∃ V : B.left.affineOpens, γ.left x.underlying ∈ V.1 ∧ V.1 ≤ U ∧
      ∀ i : I, (∀ j, Point.map (g3_proj Z (q + 1) j) x ≠ marks i) →
        (s2c_branchIdeal Z B q γ (marks i)).ideal V = ⊤ := by
  letI : Surjective γ.left := s2e_c11_surjective_of_complex_points _ _ γ
    γ.left.isClosedMap.isClosed_range hsurj
  obtain ⟨V, hxV, hVU, hunit⟩ := s2v_l1b_finite_branch_avoidance
    (fun i => s2c_branchIdeal Z B q γ (marks i)) (γ.left x.underlying) U hx
  refine ⟨V, hxV, hVU, fun i hi => ?_⟩
  exact hunit i (s2e_branch_support_excludes_unmarked_tuple Z B q γ hγ hquot x (marks i) hi)

end HodgeLean.Foundations.Program
