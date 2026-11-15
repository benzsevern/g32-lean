import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs

/-! # Local equations and their actual conormal classes -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The ideal inclusion into the ambient structure module.
Source: Hartshorne, Algebraic Geometry, II.5, ideal sheaves of closed immersions. -/
def conormalIdealInclusion {Q W : Scheme} (i : Q ⟶ W) :
    Conormal.idealModule i ⟶ SheafOfModules.unit W.ringCatSheaf :=
  kernel.ι _

/-- The regular function underlying a local ideal section, using the actual kernel inclusion.
Source: Hartshorne, Algebraic Geometry, II.5, ideal sheaves as submodules of the structure sheaf. -/
def conormalLocalFunction {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) : Γ(W.left, U) :=
  U.topIso.hom (((s ≫ (Scheme.Modules.pullback U.ι).map (conormalIdealInclusion i.left) ≫
    SheafOfModules.pullbackObjUnitToUnit U.ι.toRingCatSheafHom).val.app
      (Opposite.op (⊤ : U.toScheme.Opens))) (1 : Γ(U.toScheme, ⊤)))

/-- Specialize a local ideal section and pass to the actual conormal fibre via pullback composition.
Source: Hartshorne, Algebraic Geometry, II.8, the class of f in I/I². -/
def conormalLocalClass {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj (Conormal.sheaf i.left)) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    ((Scheme.Modules.pullbackComp x.left i.left).inv.app (Conormal.idealModule i.left))
      (moduleSectionValue (Conormal.idealModule i.left) U s (Point.map i x) hx)

/-- The coordinate derivative of the actual regular local equation at the retained ambient point.
Source: Griffiths–Harris, Principles of Algebraic Geometry, ch. 3.4, normal-conormal pairing. -/
def conormalLocalDerivative {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) (x : ComplexPoint Q) :
    (Fin d → ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (fun v => Point.evaluate U (conormalLocalFunction i U s)
    ((localChart W d (Point.map i x)).symm v))
    (localChart W d (Point.map i x) (Point.map i x))

example {Q W : Scheme} (i : Q ⟶ W) : conormalIdealInclusion i = kernel.ι _ := rfl
example {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    conormalLocalFunction i U s =
      U.topIso.hom (((s ≫ (Scheme.Modules.pullback U.ι).map (conormalIdealInclusion i.left) ≫
        SheafOfModules.pullbackObjUnitToUnit U.ι.toRingCatSheafHom).val.app
          (Opposite.op (⊤ : U.toScheme.Opens))) (1 : Γ(U.toScheme, ⊤))) := rfl
example {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U) :
    conormalLocalClass i U s x hx =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullbackComp x.left i.left).inv.app (Conormal.idealModule i.left))
          (moduleSectionValue (Conormal.idealModule i.left) U s (Point.map i x) hx) := rfl
example {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (U : W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) (x : ComplexPoint Q) :
    conormalLocalDerivative i d U s x 0 = 0 := map_zero _

#print axioms conormalLocalFunction
#print axioms conormalLocalClass
#print axioms conormalLocalDerivative
end HodgeLean.Foundations.Program.G32Native
