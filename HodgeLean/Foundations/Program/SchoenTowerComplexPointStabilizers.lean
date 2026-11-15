import HodgeLean.Foundations.Program.SchoenTowerOverSections
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program

/-- Stabilizing an actual complex point is equivalent to stabilizing its underlying
scheme point for a finite-type complex scheme. -/
theorem s2t_complexPoint_stabilizer (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (G : Type) [Group G] (ρ : G →* Aut X) (p : ComplexPoint X) (g : G) :
    (ρ g).asIso.hom.left (p.left (IsLocalRing.closedPoint ℂ)) =
        p.left (IsLocalRing.closedPoint ℂ) ↔
      p ≫ (ρ g).asIso.hom = p := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    exact ext_of_apply_closedPoint_eq X.hom (Over.w (p ≫ (ρ g).asIso.hom)) (Over.w p) h
  · intro h
    exact congrArg (fun k : ComplexPoint X => k.left (IsLocalRing.closedPoint ℂ)) h

end HodgeLean.Foundations.Program
