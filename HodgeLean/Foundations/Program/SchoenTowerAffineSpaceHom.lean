import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import HodgeLean.Foundations.Program.SchoenTowerOverSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs

namespace HodgeLean.Foundations.Program

/-- Morphisms over the complex base into affine space are specified by their actual
global coordinate sections. -/
def s2t_affineSpaceOverHomEquiv (X : Over (Spec ↧ℂ)) (ι : Type) :
    (X ⟶ Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ)) ≃ (ι → Γ(X.left, ⊤)) := by
  refine
    { toFun := fun f i => f.left.appTop (AffineSpace.coord (Spec ↧ℂ) i)
      invFun := fun v => Over.homMk (AffineSpace.homOfVector X.hom v)
        (AffineSpace.homOfVector_over X.hom v)
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · exact (AffineSpace.homOfVector_over X.hom _).trans (Over.w f).symm
    · intro i
      exact AffineSpace.homOfVector_appTop_coord X.hom _ i
  · intro v
    funext i
    exact AffineSpace.homOfVector_appTop_coord X.hom v i

/-- The coordinate equivalence evaluates its inverse on each actual affine coordinate. -/
theorem s2t_affineSpaceOverHomEquiv_symm_coord (X : Over (Spec ↧ℂ)) (ι : Type)
    (v : ι → Γ(X.left, ⊤)) (i : ι) :
    ((s2t_affineSpaceOverHomEquiv X ι).symm v).left.appTop
      (AffineSpace.coord (Spec ↧ℂ) i) = v i := by
  exact AffineSpace.homOfVector_appTop_coord X.hom v i

end HodgeLean.Foundations.Program
