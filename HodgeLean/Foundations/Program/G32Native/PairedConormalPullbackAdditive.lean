import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitFreeProjectionDetection
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Additivity of the actual scheme-module pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual scheme-module pullback retains finite coordinate resolutions by additivity. -/
theorem conormal_scheme_pullback_additive {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Additive := by
  let F := Scheme.Modules.pullback f
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts F

end HodgeLean.Foundations.Program.G32Native
