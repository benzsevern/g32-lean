import HodgeLean.Foundations.Program.SchoenCycleC11DegreeHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2FiniteDimensionHelpers
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Adapters.AbelianPower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The actual iterated power of an integral smooth complex curve has
Krull dimension equal to its number of factors. -/
theorem s2e_curve_power_krull_dimension
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    (hdim : dim Z.left = 1) (n : ℕ) :
    topologicalKrullDim (g3_power Z n).left = n := by
  let : GeometricallyIntegral Z.hom := spec_g3b_geometricallyIntegral Z
  let : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (dim Z.left) Z.hom)
  let : SmoothOfRelativeDimension n (g3_power Z n).hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power Z 1 n
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  exact SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := (g3_power Z n).hom)

/-- A finite quotient of the actual curve power has the same dimension;
complex-point surjectivity suffices on a finite-type target. -/
theorem s2e_finite_curve_power_target_dimension
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B.left] [LocallyOfFiniteType B.hom]
    (hdim : dim Z.left = 1) (n : ℕ) (γ : g3_power Z n ⟶ B)
    [IsFinite γ.left] (hs : Function.Surjective (Point.map γ)) :
    dim B.left = n := by
  let : Surjective γ.left :=
    s2e_c11_surjective_of_complex_points _ _ γ γ.left.isClosedMap.isClosed_range hs
  have he := s2e_finite_surjective_krull_dimension γ.left
  unfold TopologicalSpace.dim
  rw [← he, s2e_curve_power_krull_dimension Z hdim n]
  simp

end HodgeLean.Foundations.Program
