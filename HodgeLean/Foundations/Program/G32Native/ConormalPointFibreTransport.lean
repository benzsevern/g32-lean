import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation

/-! # Pointwise pullback composition on the actual ideal and conormal fibres -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The conormal fibre at the source point is the ideal-module fibre at the
original ambient point, by the actual pullback-composition comparison. -/
def conormalPointFibreEquiv {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (x : ComplexPoint Q) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj (Conormal.sheaf i.left)) ≃ₗ[ℂ]
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Point.map i x).left).obj (Conormal.idealModule i.left)) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullbackComp x.left i.left).app (Conormal.idealModule i.left))).toLinearEquiv

/-- The actual local conormal class is the inverse image of its original ideal
section specialization under pullback composition. -/
theorem conormalPointFibreEquiv_localClass {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U) :
    conormalPointFibreEquiv i x (conormalLocalClass i U s x hx) =
      moduleSectionValue (Conormal.idealModule i.left) U s (Point.map i x) hx := by
  exact (conormalPointFibreEquiv i x).apply_symm_apply _

/-- Dualizing the actual point-fibre comparison retains the ambient ideal
functional and the original source point. -/
def conormalPointDualEquiv {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (x : ComplexPoint Q) :
    normalFibreOfModule (Conormal.sheaf i.left) x ≃ₗ[ℂ]
      normalFibreOfModule (Conormal.idealModule i.left) (Point.map i x) :=
  (conormalPointFibreEquiv i x).symm.dualMap

/-- Evaluation of the transported dual on the original ideal section is the
original functional's value on its actual conormal class. -/
theorem conormalPointDualEquiv_localClass {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U)
    (ν : normalFibreOfModule (Conormal.sheaf i.left) x) :
    conormalPointDualEquiv i x ν
      (moduleSectionValue (Conormal.idealModule i.left) U s (Point.map i x) hx) =
      ν (conormalLocalClass i U s x hx) := rfl

#print axioms conormalPointDualEquiv
#print axioms conormalPointDualEquiv_localClass
#print axioms conormalPointFibreEquiv
#print axioms conormalPointFibreEquiv_localClass
end HodgeLean.Foundations.Program.G32Native
