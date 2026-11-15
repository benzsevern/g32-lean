import HodgeLean.Foundations.Program.SchoenCycleC2DimensionHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Every nonempty scheme open of a smooth integral complex scheme retains
its dimension. -/
theorem s2e_smooth_open_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    letI : Nonempty U := hU.to_subtype
    dim U.toScheme = dim X.left := by
  let : Nonempty U := hU.to_subtype
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : SmoothOfRelativeDimension (dim X.left) (U.ι ≫ X.hom) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + dim X.left) (U.ι ≫ X.hom))
  exact SmoothOfRelativeDimension.dim_eq (f := U.ι ≫ X.hom) (dim X.left)

end HodgeLean.Foundations.Program
