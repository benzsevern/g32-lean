import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.LocalOrientationNeighborhood
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing

/-! Canonical coherent rational orientations on smooth complex scheme point spaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem chart_local_homology_concentrated {M : Type} [TopologicalSpace M] [T1Space M]
    (d : ℕ) (E : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ E.source)
    (i : ℕ) (hi : i ≠ 2 * d) :
    Subsingleton (RelativeHomology ℚ (pointComplementPair x) i) := by
  have ht : Function.Bijective
      (relativeHomologyMap ℚ i (standardComplexChartTargetPairIso d E x hx).hom) :=
    (ConcreteCategory.isIso_iff_bijective
      ((relativeHomologyFunctor ℚ i).map (standardComplexChartTargetPairIso d E x hx).hom)).mp
      inferInstance
  have he := neighborhoodPointComplement_relativeHomologyMap_bijective
    (chartModelEmbedding d E x hx).target x (chartModelEmbedding d E x hx).open_target
    (chartModelEmbedding_mem_target d E x hx) i
  have hsur : Function.Surjective (relativeHomologyMap ℚ i
      (chartModelEmbeddingPair d E x hx)) := by
    rw [← standardComplexChartTargetPairIso_hom_comp_neighborhoodMap d E x hx,
      relativeHomologyMap_comp]
    exact (he.comp ht).2
  letI := ModuleCat.subsingleton_of_isZero (standardComplexLocalHomology_isZero_of_ne d i hi)
  exact hsur.subsingleton

def smoothLocalRationalOrientation (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T1Space (ComplexPoint X)] :
    LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d) where
  generator := complexLocalOrientation X d
  generates := by
    intro x
    have hn : complexLocalOrientation X d x ≠ 0 :=
      localClassOfChart_ne_zero d (localChart X d x) x (mem_localChart_source X d x)
    refine ⟨smul_left_injective ℚ hn, fun v => Submodule.mem_span_singleton.mp ?_⟩
    rw [span_complexLocalOrientation_eq_top]
    exact Submodule.mem_top
  vanishes := fun x i hi => chart_local_homology_concentrated d (localChart X d x) x
    (mem_localChart_source X d x) i hi
  coherent := exists_neighborhood_complexLocalOrientation X d

#print axioms chart_local_homology_concentrated
#print axioms smoothLocalRationalOrientation
end HodgeLean.Foundations.QuotientDuality
