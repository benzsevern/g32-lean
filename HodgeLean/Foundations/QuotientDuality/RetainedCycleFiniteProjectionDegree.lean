import HodgeLean.Adapters.IntersectionProductScaf
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionPointFormula
import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicNonvanishing
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

/-! Positive top-class image for the specified finite projective projection. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified finite projection is a morphism over the original complex base. -/
def retained_presentation_projection_over
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {m : ℕ}
    {ℓ : Matrix (Fin (m+1)) (Fin (D.ambientDimension+1)) ℂ}
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) : X ⟶ a3h_PnO m :=
  Over.homMk (retained_presentation_π X D hfin) (retained_presentation_π_fst X D hfin)

/-- Finite projection of an integral projective scheme has nonzero intrinsic top-class image.
Source: Fulton, Intersection Theory, §1.4, proper generic degree. -/
lemma retained_presentation_projection_intrinsic_image_ne_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) (d : ℕ)
    (hdim : topologicalKrullDim X.left = (d : ℕ))
    {ℓ : Matrix (Fin (d+1)) (Fin (D.ambientDimension+1)) ℂ}
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) :
    homologyMap ℚ (2*d)
      (TopCat.ofHom (Point.continuousMap (retained_presentation_projection_over X D hfin)))
      (properCycle_intrinsic_class X d hdim) ≠ 0 := by
  let W := a3h_PnO d
  letI : IsIntegral W.left := IntersectionProductScaf_projective_integral d
  letI : IsProjective W.hom := s0_projective_space_projective d (Spec ↧ℂ)
  let f : X ⟶ W := retained_presentation_projection_over X D hfin
  letI : IsFinite f.left := retained_presentation_π_isFinite X D hfin
  have hsur : Function.Surjective f.left :=
    retained_presentation_π_surjective X D hfin
      (retained_presentation_cone_dimension X D d hdim)
  have hg : f.left (genericPoint X.left) = genericPoint W.left := by
    obtain ⟨u, hu⟩ := hsur (genericPoint W.left)
    have hs := (genericPoint_specializes u).map f.left.continuous
    rw [hu] at hs
    exact (hs.antisymm (genericPoint_specializes _)).eq
  have hdeg : 0 < a1p_degree f.left (genericPoint X.left) :=
    (a1p_degree_pos_iff f _).mpr (IntersectionProductScaf_finite_height f.left _)
  exact retained_intrinsic_proper_image_ne_zero X W f d hdim
    (s0_complex_projective_krull_dimension d) hg hdeg

end HodgeLean.Foundations.QuotientDuality
