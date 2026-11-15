import HodgeLean.Foundations.QuotientDuality.ProperCycleSplitChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicPositiveComponentDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicContractedImage
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClass
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension

/-! # Proper residue degree on specified intrinsic component classes

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Proper pushforward of the specified intrinsic component class has the actual residue-field degree. Components with smaller-dimensional image contribute zero in this degree.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
theorem properCycle_intrinsic_component_degree_aux
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (k : ℕ)
    (hdimX : TopologicalSpace.dim X.left = 2 * k)
    (hdimY : TopologicalSpace.dim Y.left = 2 * k)
    (ξ : X.left) (hcodim : Order.coheight ξ = k) :
    homologyMap ℚ (2 * k) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_component X k ξ) =
      (a1p_degree f.left ξ : ℚ) • properCycle_intrinsic_component Y k (f.left ξ) := by
  by_cases hdegree : 0 < a1p_degree f.left ξ
  · exact properCycle_intrinsic_component_degree_pos f k hdimX hdimY ξ hcodim hdegree
  · have hzero : a1p_degree f.left ξ = 0 := Nat.eq_zero_of_not_pos hdegree
    rw [hzero, Nat.cast_zero, zero_smul]
    exact properCycle_intrinsic_component_contracted_image_zero f k hdimX ξ hcodim hzero

example := ProperCycleSplitChecks.intrinsic_component_degree_homology_example

end HodgeLean.Foundations.QuotientDuality
