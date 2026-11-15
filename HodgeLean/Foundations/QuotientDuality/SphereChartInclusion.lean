import HodgeLean.Foundations.QuotientDuality.SphereOrientationGeometry
import HodgeLean.Foundations.QuotientDuality.LocalClassCoefficients

/-! The finite sphere chart identifies its local class with the plane local class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.QuotientDuality
attribute [local instance] b4cov_sphChartedSpace

def spherePlaneInclusion : TopCat.of ℂ ⟶ TopCat.of (OnePoint ℂ) :=
  TopCat.ofHom ⟨((↑) : ℂ → OnePoint ℂ), OnePoint.continuous_coe⟩

def spherePlanePair : pointComplementPair (0 : ℂ) ⟶
    pointComplementPair ((0 : ℂ) : OnePoint ℂ) :=
  imagePointPairMap spherePlaneInclusion OnePoint.coe_injective 0

theorem sphere_chartRadius_eq :
    chartRadius 1 (b6m_surfaceChart ((0 : ℂ) : OnePoint ℂ)) ((0 : ℂ) : OnePoint ℂ)
      (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ ((0 : ℂ) : OnePoint ℂ)) =
    chartRadius 1 (b6m_surfaceChart (0 : ℂ)) (0 : ℂ)
      (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ (0 : ℂ)) := by
  unfold chartRadius
  simp only [b6m_surfaceChart, b4cov_chartAt_coe, chartAt_self_eq,
    OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.refl_apply, b4cov_chart0_coe]

theorem sphere_chartEmbedding_coe (z : Fin 1 → ℂ) :
    chartModelEmbedding 1 (b6m_surfaceChart ((0 : ℂ) : OnePoint ℂ))
      ((0 : ℂ) : OnePoint ℂ)
      (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ ((0 : ℂ) : OnePoint ℂ)) z =
    ((chartModelEmbedding 1 (b6m_surfaceChart (0 : ℂ)) 0
      (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ (0 : ℂ)) z : ℂ) : OnePoint ℂ) := by
  simp only [chartModelEmbedding, OpenPartialHomeomorph.trans_apply, sphere_chartRadius_eq]
  simp only [b6m_surfaceChart, b4cov_chartAt_coe, chartAt_self_eq,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, b4cov_chart0_symm,
    b4cov_chart0_coe]
  rfl

theorem sphere_surfacePair_eq :
    b6m_surfaceLocalPairMap (0 : ℂ) ≫ spherePlanePair =
      b6m_surfaceLocalPairMap ((0 : ℂ) : OnePoint ℂ) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    exact (sphere_chartEmbedding_coe _).symm
  · ext z
    exact (sphere_chartEmbedding_coe _).symm

theorem sphere_plane_localClass (R : Type) [CommRing R] :
    relativeHomologyMap R 2 spherePlanePair (b6m_surfaceLocalClass R (0 : ℂ)) =
      b6m_surfaceLocalClass R ((0 : ℂ) : OnePoint ℂ) := by
  rw [b6m_surfaceLocalClass_eq_image, b6m_surfaceLocalClass_eq_image,
    ← LinearMap.comp_apply, ← relativeHomologyMap_comp, sphere_surfacePair_eq]

#print axioms sphere_plane_localClass
end HodgeLean.Foundations.QuotientDuality
