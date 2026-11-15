import HodgeLean.Foundations.Program.G32Native.ModuleSectionValueUnit

/-! # Original module section values through a specified open point factorization -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Any specified factorization of the original point through its actual
open gives the original local module section value. -/
theorem moduleSectionValue_factorization {W : Over (Spec ↧ℂ)} (M : W.left.Modules)
    (U : W.left.Opens) (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (p : ComplexPoint W) (hp : p ∈ Point.overOpen U)
    (q : Spec ↧ℂ ⟶ U.toScheme) (hq : q ≫ U.ι = p.left) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((pullbackUnit q).inv ≫ (Scheme.Modules.pullback q).map s ≫
        (Scheme.Modules.pullbackComp q U.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr hq).hom.app M)
      (1 : Γ(Spec ↧ℂ, ⊤)) = moduleSectionValue M U s p hp := by
  have ha : q = liftToOpen W U p hp :=
    (cancel_mono U.ι).mp (hq.trans (liftToOpen_fac W U p hp).symm)
  subst q
  rfl

#print axioms moduleSectionValue_factorization
end HodgeLean.Foundations.Program.G32Native
