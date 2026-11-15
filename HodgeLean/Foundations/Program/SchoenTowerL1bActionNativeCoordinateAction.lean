import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeConjugacy
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeIdentity

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The inverse of the centered scalar native chart is the native curve
used in the derivative statement. -/
theorem s2v_l1b_action_centered_native_inverse
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (z : ℂ) :
    (s2v_l1b_action_centerChart (s2v_l1b_action_nativePlaneChart Y p) p).symm z =
      s2e_u1_nativeCurve Y p z := by
  change (ComplexPoint.localChart Y 1 p).symm
    (fun _ : Fin 1 => z + ComplexPoint.localChart Y 1 p p 0) =
      (ComplexPoint.localChart Y 1 p).symm
        (fun i : Fin 1 => ComplexPoint.localChart Y 1 p p i + z)
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi, add_comm]

/-- The action in the centered scalar native chart is exactly the function
whose derivative occurs in the local rotation statement. -/
theorem s2v_l1b_action_centered_native_action
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (z : ℂ) :
    let D := s2v_l1b_action_centerChart (s2v_l1b_action_nativePlaneChart Y p) p
    D (Point.map f (D.symm z)) =
      ComplexPoint.localChart Y 1 p (Point.map f (s2e_u1_nativeCurve Y p z)) 0 -
        ComplexPoint.localChart Y 1 p p 0 := by
  dsimp only
  rw [s2v_l1b_action_centered_native_inverse]
  rfl

end HodgeLean.Foundations.Program
