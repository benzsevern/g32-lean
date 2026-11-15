import HodgeLean.Foundations.Program.CycleFoundationsDimension

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The dimension of the actual product of two smooth projective varieties.
Source: Hartshorne, Algebraic Geometry, III.10, smooth relative dimensions and base change. -/
theorem s4_selected_product_dimension
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a)
    (hY : TopologicalSpace.dim Y.left = d) :
    TopologicalSpace.dim (A ⊗ Y).left = a + d := by
  letI : SmoothOfRelativeDimension a A.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
    rwa [hA] at h
  letI : SmoothOfRelativeDimension d Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  letI : SmoothOfRelativeDimension d (fst A Y).left :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.fst A.hom Y.hom))
  letI : SmoothOfRelativeDimension (a + d) (A ⊗ Y).hom := by
    have h : SmoothOfRelativeDimension (d + a) ((fst A Y).left ≫ A.hom) := inferInstance
    rwa [Over.w (fst A Y), Nat.add_comm d a] at h
  exact SmoothOfRelativeDimension.dim_eq (f := (A ⊗ Y).hom) (a + d)

#print axioms s4_selected_product_dimension

end HodgeLean.Foundations.Program
