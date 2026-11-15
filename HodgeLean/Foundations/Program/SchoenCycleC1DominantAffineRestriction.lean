import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every nonempty affine source restriction of the actual dominant
projection retains an injective map from the specified base sections. -/
theorem s2e_c1_dominant_appLE_injective
    {X Y : Scheme} [IsIntegral X] [IsReduced Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    (U : Y.Opens) (V : X.Opens) [Nonempty V] (hVU : V ≤ f ⁻¹ᵁ U) :
    Function.Injective (f.appLE U V hVU) := by
  haveI : IsSchemeTheoreticallyDominant f := .of_isDominant f
  exact (map_injective_of_isIntegral X (homOfLE hVU)).comp (f.app_injective U)

end HodgeLean.Foundations.Program
