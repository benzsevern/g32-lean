import HodgeLean.Foundations.Program.SchoenCycleBranchImagePoints
import HodgeLean.Foundations.Program.SchoenCycleIdealSupportNeighbourhood

/-! # The branch ideal off the marked support -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An actual quotient tuple without the mark avoids the support of the insertion kernel.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_branch_support_excludes_unmarked_tuple
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left]
    (q : ℕ) (γ : g3_power Z (q + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (q + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (q + 1) ⟶ T),
      (∀ σ, s2_permute Z (q + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z (q + 1))) (p : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z (q + 1) i) x ≠ p) :
    γ.left x.underlying ∉ (s2c_branchIdeal Z B q γ p).support := by
  let ins := s2c_branchInsertion Z q p
  letI : IsClosedImmersion ins.left := s2e_branchInsertion_isClosedImmersion Z q p
  letI : IsFinite (ins ≫ γ).left := by
    change IsFinite (ins.left ≫ γ.left)
    infer_instance
  intro hmem
  change γ.left x.underlying ∈ ((ins ≫ γ).left.ker.support : Set B.left) at hmem
  rw [Scheme.Hom.support_ker,
    (ins ≫ γ).left.isClosedMap.isClosed_range.closure_eq] at hmem
  obtain ⟨z, hz⟩ := s2e_complexPoint_lift_of_mem_range (ins ≫ γ) (Point.map γ x) hmem
  obtain ⟨σ, hσ⟩ := s2e_step1_finite_quotient_point_orbits
    (g3_power Z (q + 1)) B (Equiv.Perm (Fin (q + 1)))
    (s2_permute Z (q + 1)) (s2e_step1_permute_one Z (q + 1))
    (s2e_step1_permute_mul Z (q + 1)) γ hγ hquot x (Point.map ins z) hz.symm
  apply hx (σ.symm 0)
  have he := congrArg (Point.map (g3_proj Z (q + 1) 0)) hσ
  change x ≫ (s2_permute Z (q + 1) σ ≫ g3_proj Z (q + 1) 0) =
    z ≫ (ins ≫ g3_proj Z (q + 1) 0) at he
  have hproj : s2_permute Z (q + 1) σ ≫ g3_proj Z (q + 1) 0 =
      g3_proj Z (q + 1) (σ.symm 0) := s2_check_lift_proj _ _ _
  rw [hproj, show ins ≫ g3_proj Z (q + 1) 0 =
    CartesianMonoidalCategory.toUnit _ ≫ p from s2_check_lift_proj _ _ 0,
    ← Category.assoc] at he
  have hu : z ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit).hom_ext _ _
  change x ≫ g3_proj Z (q + 1) (σ.symm 0) = p
  simpa only [hu, Category.id_comp] using he

end HodgeLean.Foundations.Program
