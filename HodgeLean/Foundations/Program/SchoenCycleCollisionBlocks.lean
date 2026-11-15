import HodgeLean.Foundations.Program.SchoenCycleInvariantParameterDescent
import HodgeLean.Foundations.Program.SchoenCycleBlockElementary

/-! # Collision blocks of actual fixed power points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A permutation fixing an actual curve-power point preserves each collision
block of its projected complex points.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_fixed_tuple_collision_block
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (x : ComplexPoint (g3_power Z n))
    (p : ComplexPoint Z) (σ : Equiv.Perm (Fin n))
    (hσ : Point.map (s2_permute Z n σ) x = x) (i : Fin n) :
    Point.map (g3_proj Z n i) x = p ↔ Point.map (g3_proj Z n (σ i)) x = p := by
  have he := congrArg (Point.map (g3_proj Z n (σ i))) hσ
  change Point.map (s2_permute Z n σ ≫ g3_proj Z n (σ i)) x =
    Point.map (g3_proj Z n (σ i)) x at he
  have hproj : s2_permute Z n σ ≫ g3_proj Z n (σ i) =
      g3_proj Z n (σ.symm (σ i)) := s2_check_lift_proj n _ (σ i)
  rw [hproj, σ.symm_apply_apply] at he
  rw [he]

end HodgeLean.Foundations.Program
