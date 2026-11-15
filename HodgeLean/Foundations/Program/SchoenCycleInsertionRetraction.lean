import HodgeLean.Foundations.Program.SchoenCycleSymmetricBranch
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

/-! # Coordinate retraction of actual marked insertion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Drop the marked first coordinate of a retained scheme power.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
def s2e_dropFirstPowerCoordinate (Z : Over (Spec ↧ℂ)) (n : ℕ) :
    g3_power Z (n + 1) ⟶ g3_power Z n :=
  s2_lift n (fun i => g3_proj Z (n + 1) i.succ)

/-- Deleting the marked coordinate retracts actual marked insertion.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_branchInsertion_retraction
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (a : ComplexPoint Z) :
    s2c_branchInsertion Z n a ≫ s2e_dropFirstPowerCoordinate Z n = 𝟙 (g3_power Z n) := by
  apply s2e_power_hom_ext
  intro i
  have hd : s2e_dropFirstPowerCoordinate Z n ≫ g3_proj Z n i =
      g3_proj Z (n + 1) i.succ := s2_check_lift_proj n _ i
  have hq : s2c_branchInsertion Z n a ≫ g3_proj Z (n + 1) i.succ =
      g3_proj Z n i := s2_check_lift_proj (n + 1) _ i.succ
  rw [Category.assoc, hd, hq, Category.id_comp]

end HodgeLean.Foundations.Program
