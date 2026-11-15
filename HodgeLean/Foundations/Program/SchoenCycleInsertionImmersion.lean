import HodgeLean.Foundations.Program.SchoenCycleInsertionRetraction
import HodgeLean.Foundations.SegreProjective

/-! # Scheme immersion of actual marked insertion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Actual marked insertion is an immersion with proper image in the
projective curve power.
Source: Hartshorne, Algebraic Geometry, II.4, sections of separated morphisms;
Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_branchInsertion_isClosedImmersion
    (Z : Over (Spec ↧ℂ)) [IsProjective Z.hom] (n : ℕ) (a : ComplexPoint Z) :
    IsClosedImmersion (s2c_branchInsertion Z n a).left := by
  let q := s2c_branchInsertion Z n a
  let d := s2e_dropFirstPowerCoordinate Z n
  have hr : q.left ≫ d.left = 𝟙 (g3_power Z n).left :=
    congrArg Over.Hom.left (s2e_branchInsertion_retraction Z n a)
  letI : IsSeparated (d.left ≫ (g3_power Z n).hom) := by
    rw [Over.w d]
    infer_instance
  letI : IsSeparated d.left := IsSeparated.of_comp d.left (g3_power Z n).hom
  letI : IsClosedImmersion (q.left ≫ d.left) := by
    rw [hr]
    infer_instance
  exact IsClosedImmersion.of_comp q.left d.left

end HodgeLean.Foundations.Program
