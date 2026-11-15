import HodgeLean.Foundations.Program.G32Native.PairedResidualLastFibre
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The conormal supplied by a product ruling of the residual component -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A residual product with a smooth base has a smooth projection to the
curve. A marked fibre of that projection supplies the intersection
conormal, pushed to its actual hyperplane image.
Source: Hartshorne, Algebraic Geometry, II.8, conormal base change;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7.
The actual product square and marked fibre square are arguments. -/
def pairedLastProductRulingConormal
    {R D C : Over (Spec ↧ℂ)} [Smooth D.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    (q : R ⟶ D) (g : R ⟶ C)
    (product : IsPullback q.left g.left D.hom C.hom)
    (c : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) [IsClosedImmersion c.left]
    {S P H : Scheme.{0}}
    (s : S ⟶ R.left) [IsClosedImmersion s] (p : S ⟶ Spec ↧ℂ)
    (fibre : IsPullback p s c.left g.left)
    (a : S ⟶ P) (h : H ⟶ P) (e : S ≅ H) (he : e.hom ≫ h = a) :
    (Scheme.Modules.pushforward a).obj (s2c_conormal s) ≅
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit H.ringCatSheaf) := by
  letI : Smooth g.left := MorphismProperty.of_isPullback (P := @Smooth) product
    (inferInstance : Smooth D.hom)
  exact residual_flat_curve_last_iso C c s g.left p fibre a h e he

#print axioms pairedLastProductRulingConormal

end HodgeLean.Foundations.Program.G32Native
