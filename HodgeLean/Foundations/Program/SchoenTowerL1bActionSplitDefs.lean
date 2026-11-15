import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceOrientation

/-! # Integral local orientation classes for the L1b comparison
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The native complex orientation class of a smooth algebraic curve, in degree two.
Source: Miranda, Algebraic Curves and Riemann Surfaces, III.3, complex local coordinates. -/
def s2v_l1b_action_curveLocalClass (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1) (p : ComplexPoint Y) :
    RelativeHomology ℤ (pointComplementPair p) 2 := by
  simpa only [hdimY, mul_one] using
    (b6m_manifoldLocalClass ℤ (TopologicalSpace.dim Y.left) p)

example (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1) (p : ComplexPoint Y) :
    RelativeHomology ℤ (pointComplementPair p) 2 :=
  s2v_l1b_action_curveLocalClass Y hdimY p

end HodgeLean.Foundations.Program
