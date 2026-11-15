import HodgeLean.Foundations.Program.G32Native.CanonicalConormalFibreEquiv
import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeAllOpens

/-! # All original local equations in the retained canonical normal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified canonical normal representative retains the derivative
of every original ideal equation on every original ambient open. -/
theorem canonicalConormalFibreEquiv_localEquation (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (ν : canonicalNormalFibre G x) (U : G.W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left))
    (hx : Point.map G.ι x ∈ Point.overOpen U) :
    ν (conormalLocalClass G.ι U s x hx) =
      conormalLocalDerivative G.ι (G.k + G.k) U s x (canonicalConormalFibreEquiv G x ν).val := by
  let D := localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)
  have hD : IsAffineOpen D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
      using D.isAffine
  have hxD : Point.map G.ι x ∈ Point.overOpen D.ambientCoordinateOpen := by
    simpa only [Point.overOpen, Set.mem_setOf_eq, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using D.mem
  have h := congrArg (fun f : canonicalNormalFibre G x => f (conormalLocalClass G.ι U s x hx))
    (canonicalConormalFibreEquiv_pairing G x ν)
  exact h.symm.trans (conormalPointDerivativeMap_localEquation G.ι (G.k + G.k) x
    D.ambientCoordinateOpen hD hxD U s hx (canonicalConormalFibreEquiv G x ν).val)

#print axioms canonicalConormalFibreEquiv_localEquation
end HodgeLean.Foundations.Program.G32Native
