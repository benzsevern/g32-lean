import HodgeLean.Foundations.Program.G32Native.ConormalLocalFunctionRestriction
import HodgeLean.Foundations.Program.G32Native.AnalyticPointDerivation

/-! # Original local equation derivatives under ambient open restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of an original local ideal equation retains its derivative
in the original ambient chart at the original point. -/
theorem conormalLocalDerivative_restrict {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (d : ℕ) [SmoothOfRelativeDimension d W.hom] (U V : W.left.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hxV : Point.map i x ∈ Point.overOpen V) (v : Fin d → ℂ) :
    conormalLocalDerivative i d V
      (moduleSectionRestrict (Conormal.idealModule i.left) U V hVU s) x v =
    conormalLocalDerivative i d U s x v := by
  have hg := s2e_regularSection_nativeAnalyticGerm_restrict W d (Point.map i x)
    U V hVU hxV (conormalLocalFunction i U s)
  have hd := congrArg (fun z => s2e_nativeAnalyticGerm_value d
    (s2e_nativeAnalytic_derivation d v z)) hg
  change analyticPointDerivation d v
    (s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) U (hVU hxV))
    (conormalLocalFunction i U s) =
    analyticPointDerivation d v (s2e_regularSection_nativeAnalyticGerm W d (Point.map i x) V hxV)
      (W.left.presheaf.map (homOfLE hVU).op (conormalLocalFunction i U s)) at hd
  rw [regularSection_pointDerivative, regularSection_pointDerivative] at hd
  unfold conormalLocalDerivative
  rw [conormalLocalFunction_restrict]
  exact hd.symm

#print axioms conormalLocalDerivative_restrict
end HodgeLean.Foundations.Program.G32Native
