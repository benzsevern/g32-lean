import HodgeLean.Foundations.Program.G32Native.CanonicalConormalDerivative
import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeAllOpens

/-! # Evaluation of the actual conormal derivative on every original equation -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Every ambient tangent vector differentiates the original equation when
paired through the actual conormal derivative, on every containing open. -/
theorem canonicalConormalDerivative_localEquation (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (v : Fin (G.k + G.k) → ℂ) (U : G.W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left))
    (hx : Point.map G.ι x ∈ Point.overOpen U) :
    canonicalConormalDerivative G x v (conormalLocalClass G.ι U s x hx) =
      conormalLocalDerivative G.ι (G.k + G.k) U s x v := by
  let D := localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)
  have hD : IsAffineOpen D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using D.isAffine
  have hxD : Point.map G.ι x ∈ Point.overOpen D.ambientCoordinateOpen := by
    simpa only [Point.overOpen, Set.mem_setOf_eq, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using D.mem
  exact conormalPointDerivativeMap_localEquation G.ι (G.k + G.k) x
    D.ambientCoordinateOpen hD hxD U s hx v

#print axioms canonicalConormalDerivative_localEquation
end HodgeLean.Foundations.Program.G32Native
