import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuasiFiniteDimension
import HodgeLean.Foundations.Program.SchoenSelectedGeometryDimensionLower
import HodgeLean.Foundations.Program.SchoenFiniteMorphisms
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A finite surjective map to a smooth integral curve retains dimension one at its source. -/
theorem s4_selected_finite_curve_source_dimension
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (q : X ⟶ Y) [IsFinite q.left]
    (hq : Function.Surjective (Point.map q)) : TopologicalSpace.dim X.left = 1 := by
  letI : PartialOrder X.left := specializationOrder X.left
  letI : PartialOrder Y.left := specializationOrder Y.left
  have hy : topologicalKrullDim Y.left = 1 := by
    rw [topologicalKrullDim_eq_krullDim,
      SmoothOfRelativeDimension.orderKrullDim_eq_complex
        (f := Y.hom) (d := TopologicalSpace.dim Y.left), hdim]
    norm_num
  have hnt : Nontrivial Y.left := by
    by_contra hn
    letI : Subsingleton Y.left := not_nontrivial_iff_subsingleton.mp hn
    have hz : topologicalKrullDim Y.left = 0 := by
      rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_zero]
    exact zero_ne_one (hz.symm.trans hy)
  letI := hnt
  have hs := s2_surjective_of_point_surjective q hq
  letI : Nontrivial X.left := hs.nontrivial
  have hu : topologicalKrullDim X.left ≤ 1 := by
    simpa only [hy] using s0_quasiFinite_krull_dimension_le q.left
  have he : topologicalKrullDim X.left = 1 := by
    with_reducible exact le_antisymm hu (s0_irreducible_krull_dimension_lower X.left)
  unfold TopologicalSpace.dim
  rw [he]
  simp

#print axioms s4_selected_finite_curve_source_dimension

end HodgeLean.Foundations.Program
