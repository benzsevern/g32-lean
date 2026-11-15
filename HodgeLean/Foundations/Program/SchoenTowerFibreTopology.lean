import HodgeLean.Foundations.Program.SchoenTowerPointFibre
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_point_closedImmersion (K : Over (Spec ↧ℂ))
    [IsSeparated K.hom] (k : ComplexPoint K) : IsClosedImmersion k.left := by
  letI : IsClosedImmersion (k.left ≫ K.hom) := by
    rw [k.w]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  exact IsClosedImmersion.of_comp k.left K.hom

theorem s2v_schemeFibre_closedImmersion {E K : Over (Spec ↧ℂ)}
    [IsSeparated K.hom] (p : E ⟶ K) (k : ComplexPoint K) :
    IsClosedImmersion (pullback.fst p k).left := by
  exact MorphismProperty.of_isPullback
    (P := @IsClosedImmersion)
    (((IsPullback.of_hasPullback p k).map (Over.forget _)).flip)
    (s2v_point_closedImmersion K k)

theorem s2v_pointFibreEquiv_isEmbedding {E K : Over (Spec ↧ℂ)}
    [IsSeparated K.hom] (p : E ⟶ K) (k : ComplexPoint K) :
    Topology.IsEmbedding (s2v_pointFibreEquiv p k) := by
  letI := s2v_schemeFibre_closedImmersion p k
  exact (ComplexPoint.isEmbedding_map_of_closedImmersion (pullback.fst p k)).codRestrict
    {x : ComplexPoint E | Point.map p x = k} (fun z => (s2v_pointFibreEquiv p k z).property)

def s2v_separatedPointFibreHomeomorph {E K : Over (Spec ↧ℂ)}
    [IsSeparated K.hom] (p : E ⟶ K) (k : ComplexPoint K) :
    ComplexPoint (pullback p k) ≃ₜ {x : ComplexPoint E // Point.map p x = k} :=
  (s2v_pointFibreEquiv p k).toHomeomorphOfIsInducing
    (s2v_pointFibreEquiv_isEmbedding p k).isInducing

theorem s2v_separatedPointFibreHomeomorph_projection {E K : Over (Spec ↧ℂ)}
    [IsSeparated K.hom] (p : E ⟶ K) (k : ComplexPoint K)
    (z : ComplexPoint (pullback p k)) :
    (s2v_separatedPointFibreHomeomorph p k z).val =
      Point.map (pullback.fst p k) z := rfl

theorem s2v_schemeFibre_compact {E K : Over (Spec ↧ℂ)}
    [IsSeparated K.hom] [CompactSpace (ComplexPoint E)]
    (p : E ⟶ K) (k : ComplexPoint K) :
    CompactSpace (ComplexPoint (pullback p k)) := by
  letI := s2v_schemeFibre_closedImmersion p k
  exact (ComplexPoint.isClosedEmbedding_map_of_closedImmersion (pullback.fst p k)).compactSpace

end HodgeLean.Foundations.Program
