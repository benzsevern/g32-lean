import HodgeLean.Foundations.Program.SchoenCycleInsertionRetraction

/-! # Actual points in the marked insertion image -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A power point whose first coordinate is the mark is recovered by deleting
that coordinate and applying actual marked insertion.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_branchInsertion_point_of_first_coordinate
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (a : ComplexPoint Z)
    (x : ComplexPoint (g3_power Z (n + 1)))
    (hx : Point.map (g3_proj Z (n + 1) 0) x = a) :
    Point.map (s2c_branchInsertion Z n a) (Point.map (s2e_dropFirstPowerCoordinate Z n) x) = x := by
  let q := s2c_branchInsertion Z n a
  let d := s2e_dropFirstPowerCoordinate Z n
  change (x ≫ d) ≫ q = x
  apply s2e_power_hom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hq : q ≫ g3_proj Z (n + 1) 0 =
        CartesianMonoidalCategory.toUnit (g3_power Z n) ≫ a := s2_check_lift_proj (n + 1) _ 0
    have hu : (x ≫ d) ≫ CartesianMonoidalCategory.toUnit (g3_power Z n) = 𝟙 _ :=
      (SemiCartesianMonoidalCategory.isTerminalTensorUnit).hom_ext _ _
    calc
      ((x ≫ d) ≫ q) ≫ g3_proj Z (n + 1) 0 =
          (x ≫ d) ≫ (q ≫ g3_proj Z (n + 1) 0) := Category.assoc _ _ _
      _ = a := by rw [hq, ← Category.assoc, hu, Category.id_comp]
      _ = x ≫ g3_proj Z (n + 1) 0 := hx.symm
  · have hq : q ≫ g3_proj Z (n + 1) j.succ = g3_proj Z n j :=
      s2_check_lift_proj (n + 1) _ j.succ
    have hd : d ≫ g3_proj Z n j = g3_proj Z (n + 1) j.succ := s2_check_lift_proj n _ j
    calc
      ((x ≫ d) ≫ q) ≫ g3_proj Z (n + 1) j.succ =
          (x ≫ d) ≫ (q ≫ g3_proj Z (n + 1) j.succ) := Category.assoc _ _ _
      _ = (x ≫ d) ≫ g3_proj Z n j := by rw [hq]
      _ = x ≫ (d ≫ g3_proj Z n j) := Category.assoc _ _ _
      _ = x ≫ g3_proj Z (n + 1) j.succ := by rw [hd]

end HodgeLean.Foundations.Program
