import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Actual pullback-composition maps on original module fibres -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The two actual pullback-composition maps retain the same original
module through three specified scheme morphisms. -/
theorem pullbackComp_associativity_hom {X Y Z T : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : T.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  have he := congrArg (fun e => e.hom.app M)
    (SheafOfModules.pullback_assoc h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)
  exact he.symm

#print axioms pullbackComp_associativity_hom
end HodgeLean.Foundations.Program.G32Native
