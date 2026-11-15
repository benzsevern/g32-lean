import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeSmooth

/-! # Global smoothness from the original native submersion -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Surjectivity of the differential in the original native coordinates at
all complex points gives smoothness of the actual scheme morphism.
Source: EGA IV, 17.11.1 and 17.3.3. -/
theorem residual_native_submersion_smooth
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (ht : ∀ p : ComplexPoint X,
      Function.Surjective (fderiv ℂ (fun z : Fin d → ℂ =>
        localChart Y e (Point.map f p)
          (Point.map f ((localChart X d p).symm (localChart X d p p + z)))) 0)) :
    Smooth f.left := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  exact residual_smooth_of_complex_points X Y f
    (fun p => residual_native_submersion_mem_smoothLocus X Y d e f p (ht p))

#print axioms residual_native_submersion_smooth
end HodgeLean.Foundations.Program.G32Native
