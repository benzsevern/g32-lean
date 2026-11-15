import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitLift
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Data.Complex.Basic

/-! # Detecting actual unit arrows by the value of their global unit section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An actual arrow from the structure module is zero exactly when its value
on the global unit section is zero. -/
theorem conormal_unit_map_eq_zero_iff_top_one {X : Scheme} {M : X.Modules}
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    φ = 0 ↔ φ.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply M.unitHomEquiv.injective
    apply conormal_sections_top_injective M
    change φ.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = 0
    exact h

/-- The actual global-section functor at the complex point detects a unit arrow by the image of one. -/
theorem conormal_point_unit_map_eq_zero_iff_value
    {M : (Spec (CommRingCat.of ℂ)).Modules}
    (φ : SheafOfModules.unit (Spec (CommRingCat.of ℂ)).ringCatSheaf ⟶ M) :
    φ = 0 ↔ (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map φ
      (1 : Γ(Spec (CommRingCat.of ℂ), ⊤)) = 0 := by
  exact conormal_unit_map_eq_zero_iff_top_one φ

end HodgeLean.Foundations.Program.G32Native
