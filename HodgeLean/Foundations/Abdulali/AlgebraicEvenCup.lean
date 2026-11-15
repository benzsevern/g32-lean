import HodgeLean.Foundations.Abdulali.TensorQuadraticAlgebraicity
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan
variable (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- The actual algebraic cycle span, extended by zero in odd degrees, is cup-closed.
Source: Fulton, Intersection Theory, Corollary 19.2. -/
theorem algebraic_even_span_cup {i j k : ℕ} (h : i+j=k)
    {a : ℂ ⊗[ℚ] HQ Y i} {b : ℂ ⊗[ℚ] HQ Y j}
    (ha : a ∈ f1575EvenCohomologySpan (algebraicCycleClassSpan Y) i)
    (hb : b ∈ f1575EvenCohomologySpan (algebraicCycleClassSpan Y) j) :
    (cupProductOf Y).cupC h a b ∈
      f1575EvenCohomologySpan (algebraicCycleClassSpan Y) k := by
  exact f1575EvenCohomologySpan_cup («μ» := cupProductOf Y) (algebraicCycleClassSpan Y)
    (fun h a b ha hb => (hc9k_cycleClassMultiplicative Y).mem_of_eq h a b ha hb) h ha hb


end HodgeLean.Foundations.Abdulali
