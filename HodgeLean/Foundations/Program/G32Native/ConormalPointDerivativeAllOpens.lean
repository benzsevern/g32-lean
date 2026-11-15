import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeRestriction
import HodgeLean.Foundations.Program.G32Native.AffineOpenIntersection

/-! # All original local ideal equations in the actual conormal pairing -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual conormal pairing computed on any containing affine open
retains every original local equation on every original ambient open. -/
theorem conormalPointDerivativeMap_localEquation {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hxU : Point.map i x ∈ Point.overOpen U) (V : W.left.Opens)
    (s : unit V.toScheme ⟶ (Scheme.Modules.pullback V.ι).obj (Conormal.idealModule i.left))
    (hxV : Point.map i x ∈ Point.overOpen V) (v : Fin d → ℂ) :
    conormalPointDerivativeMap i d x U hU hxU v (conormalLocalClass i V s x hxV) =
      conormalLocalDerivative i d V s x v := by
  obtain ⟨T, hT, hxT, hTU, hTV⟩ := exists_affine_open_intersection W.left U V
    (Point.map i x).underlying hxU hxV
  have hA := conormalPointDerivativeMap_restrict i d x U T hU hT hTU hxU hxT
  let sT := moduleSectionRestrict (Conormal.idealModule i.left) V T hTV s
  have hc : conormalLocalClass i T sT x hxT = conormalLocalClass i V s x hxV :=
    conormalLocalClass_restrict i V T hTV s x hxT
  have hd : conormalLocalDerivative i d T sT x v = conormalLocalDerivative i d V s x v :=
    conormalLocalDerivative_restrict i d V T hTV s x hxT v
  rw [hA, ← hc]
  exact (conormalPointDerivativeMap_localSection i d x T hT hxT v sT).trans hd

#print axioms conormalPointDerivativeMap_localEquation
end HodgeLean.Foundations.Program.G32Native
