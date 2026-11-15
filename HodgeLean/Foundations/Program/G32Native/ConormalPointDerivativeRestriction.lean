import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeNormalization
import HodgeLean.Foundations.Program.G32Native.ConormalPointSectionsExt
import HodgeLean.Foundations.Program.G32Native.ConormalLocalRestriction
import HodgeLean.Foundations.Program.G32Native.ConormalLocalDerivativeRestriction

/-! # Original conormal point pairings on smaller ambient affine opens -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restricting to a smaller actual ambient affine open retains the same
actual conormal pairing in the original ambient chart. -/
theorem conormalPointDerivativeMap_restrict {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U V : W.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) (hxU : Point.map i x ∈ Point.overOpen U)
    (hxV : Point.map i x ∈ Point.overOpen V) :
    conormalPointDerivativeMap i d x U hU hxU = conormalPointDerivativeMap i d x V hV hxV := by
  apply LinearMap.ext
  intro v
  apply conormalLocalClasses_ext i d x U hU hxU
  intro s
  let sV := moduleSectionRestrict (Conormal.idealModule i.left) U V hVU s
  have hc : conormalLocalClass i V sV x hxV = conormalLocalClass i U s x hxU :=
    conormalLocalClass_restrict i U V hVU s x hxV
  have hd : conormalLocalDerivative i d V sV x v = conormalLocalDerivative i d U s x v :=
    conormalLocalDerivative_restrict i d U V hVU s x hxV v
  have hu := conormalPointDerivativeMap_localSection i d x U hU hxU v s
  have hv := conormalPointDerivativeMap_localSection i d x V hV hxV v sV
  rw [hc] at hv
  exact hu.trans (hd.symm.trans hv.symm)

#print axioms conormalPointDerivativeMap_restrict
end HodgeLean.Foundations.Program.G32Native
