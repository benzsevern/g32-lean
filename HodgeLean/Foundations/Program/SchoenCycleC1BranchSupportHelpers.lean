import HodgeLean.Foundations.Program.SchoenCycleInsertionPointRange
import HodgeLean.Foundations.Program.SchoenCycleBranchOffSupport

/-! # Marked coordinates in the actual branch support -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A marked coordinate puts the actual symmetric quotient point in the
support of the corresponding branch ideal. -/
theorem s2e_c1_marked_coordinate_mem_branch_support
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] [IsProjective B.hom] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z (n + 1)))
    (i : Fin (n + 1)) (hi : Point.map (g3_proj Z (n + 1) i) x = a) :
    γ.left x.underlying ∈ (s2c_branchIdeal Z B n γ a).support := by
  classical
  let σ := Equiv.swap (0 : Fin (n + 1)) i
  let u := s2_permute Z (n + 1) σ
  let y := Point.map u x
  have hy : Point.map (g3_proj Z (n + 1) 0) y = a := by
    change x ≫ (u ≫ g3_proj Z (n + 1) 0) = a
    have hp : u ≫ g3_proj Z (n + 1) 0 = g3_proj Z (n + 1) (σ.symm 0) :=
      s2_check_lift_proj _ _ _
    rw [hp]
    change x ≫ g3_proj Z (n + 1) i = a at hi
    simpa only [σ, Equiv.symm_swap, Equiv.swap_apply_left] using hi
  have hγy : Point.map γ y = Point.map γ x := by
    change (x ≫ u) ≫ γ = x ≫ γ
    rw [Category.assoc, hγ]
  let v := Point.map (s2e_dropFirstPowerCoordinate Z n) y
  have hv : Point.map (s2c_branchInsertion Z n a ≫ γ) v = Point.map γ x := by
    rw [Point.map_comp_apply]
    exact (congrArg (Point.map γ)
      (s2e_branchInsertion_point_of_first_coordinate Z n a y hy)).trans hγy
  haveI : IsProper ((s2c_branchInsertion Z n a ≫ γ).left ≫ B.hom) := by
    rw [Over.w (s2c_branchInsertion Z n a ≫ γ)]
    infer_instance
  haveI : IsProper (s2c_branchInsertion Z n a ≫ γ).left :=
    IsProper.of_comp _ B.hom
  change γ.left x.underlying ∈ (((s2c_branchInsertion Z n a ≫ γ).left.ker).support : Set B.left)
  rw [Scheme.Hom.support_ker]
  apply subset_closure
  refine ⟨v.underlying, ?_⟩
  simpa only [Point.underlying_map] using congrArg Point.underlying hv

end HodgeLean.Foundations.Program
