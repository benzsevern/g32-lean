import Mathlib.AlgebraicGeometry.Restrict

/-! # Original top-open section comparisons under open restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original top-open section identifications retain the actual
restriction map between the specified original ambient opens. -/
theorem openTopIso_restriction (X : Scheme.{0}) (U V : X.Opens) (hVU : V ≤ U) :
    U.topIso.hom ≫ X.presheaf.map (homOfLE hVU).op =
      (X.homOfLE hVU).appTop ≫ V.topIso.hom := by
  rw [Scheme.homOfLE_appTop]
  simp only [Scheme.Opens.topIso, Functor.mapIso_hom, Iso.op_hom, eqToIso.inv,
    ← Functor.map_comp]
  congr 1

#print axioms openTopIso_restriction
end HodgeLean.Foundations.Program.G32Native
