import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation
import HodgeLean.Foundations.Program.G32Native.ModuleSectionRestriction

/-! # Original conormal classes under ambient open restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restricting an original local ideal section retains its original
conormal class at the original source point. -/
theorem conormalLocalClass_restrict {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U V : W.left.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hxV : Point.map i x ∈ Point.overOpen V) :
    conormalLocalClass i V (moduleSectionRestrict (Conormal.idealModule i.left) U V hVU s) x hxV =
      conormalLocalClass i U s x (hVU hxV) := by
  unfold conormalLocalClass
  rw [moduleSectionValue_restrict]

#print axioms conormalLocalClass_restrict
end HodgeLean.Foundations.Program.G32Native
