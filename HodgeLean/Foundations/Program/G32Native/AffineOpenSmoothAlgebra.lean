import HodgeConjecture.Mathlib.AlgebraicGeometry.Over.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.Complex.Basic

/-! # Smooth original complex algebras on actual affine opens -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Sections on an actual affine open of a smooth complex scheme are
smooth with their original complex scalar structure. -/
theorem affineOpen_smoothAlgebra (W : Over (Spec ↧ℂ)) [Smooth W.hom]
    (U : W.left.Opens) (hU : IsAffineOpen U) :
    letI := overSpecAlgebra W U
    Algebra.Smooth ℂ Γ(W.left, U) := by
  letI := overSpecAlgebra W U
  apply RingHom.smooth_algebraMap.mp
  change ((W.hom.appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).Smooth
  exact RingHom.Smooth.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
    (W.hom.smooth_appLE (isAffineOpen_top _) hU (by simp))

#print axioms affineOpen_smoothAlgebra
end HodgeLean.Foundations.Program.G32Native
