import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Restriction to a nonempty source neighbourhood preserves the exact
rational value of every original section. -/
theorem s2e_c1_rational_section_restriction
    (X : Scheme) [IsIntegral X] (U V : X.Opens) [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField V ((X.presheaf.map (homOfLE hVU).op).hom s) =
      X.germToFunctionField U s := by
  change (X.presheaf.map (homOfLE hVU).op ≫ X.germToFunctionField V).hom s = _
  rw [X.presheaf.germ_res]

end HodgeLean.Foundations.Program
