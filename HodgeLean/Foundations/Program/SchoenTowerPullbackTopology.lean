import HodgeLean.Foundations.Program.SchoenTowerFibreTopology
import HodgeLean.Foundations.ComplexPointGroup

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Program

def s2v_pullbackEqualizerIso {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B) :
    pullback β j ≅ equalizer
      (CartesianMonoidalCategory.fst W E ≫ β) (CartesianMonoidalCategory.snd W E ≫ j) where
  hom := equalizer.lift
    (CartesianMonoidalCategory.lift (pullback.fst β j) (pullback.snd β j)) (by
      simp only [← Category.assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.lift_snd]
      exact pullback.condition)
  inv := pullback.lift
    (equalizer.ι _ _ ≫ CartesianMonoidalCategory.fst W E)
    (equalizer.ι _ _ ≫ CartesianMonoidalCategory.snd W E) (by
      simp only [Category.assoc]
      exact equalizer.condition _ _)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        equalizer.lift_ι_assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, equalizer.lift_ι,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd,
        pullback.lift_fst, pullback.lift_snd, Category.id_comp]

theorem s2v_pullback_toProduct_closedImmersion {W B E : Over (Spec ↧ℂ)}
    [IsSeparated B.hom] (β : W ⟶ B) (j : E ⟶ B) :
    IsClosedImmersion (CartesianMonoidalCategory.lift (pullback.fst β j)
      (pullback.snd β j)).left := by
  have h : (s2v_pullbackEqualizerIso β j).hom ≫ equalizer.ι _ _ =
      CartesianMonoidalCategory.lift (pullback.fst β j) (pullback.snd β j) :=
    equalizer.lift_ι _ _
  rw [← h]
  change IsClosedImmersion ((s2v_pullbackEqualizerIso β j).hom.left ≫
    (equalizer.ι (CartesianMonoidalCategory.fst W E ≫ β)
      (CartesianMonoidalCategory.snd W E ≫ j)).left)
  infer_instance

theorem s2v_pullback_points_compact {W B E : Over (Spec ↧ℂ)}
    [IsSeparated B.hom] [CompactSpace (ComplexPoint W)] [CompactSpace (ComplexPoint E)]
    (β : W ⟶ B) (j : E ⟶ B) : CompactSpace (ComplexPoint (pullback β j)) := by
  letI : CompactSpace (ComplexPoint (W ⊗ E)) :=
    (HodgeLean.Foundations.complexPointProdHomeomorph W E).isClosedEmbedding.compactSpace
  letI := s2v_pullback_toProduct_closedImmersion β j
  exact (ComplexPoint.isClosedEmbedding_map_of_closedImmersion
    (CartesianMonoidalCategory.lift (pullback.fst β j) (pullback.snd β j))).compactSpace

theorem s2v_pullback_points_t2 {W B E : Over (Spec ↧ℂ)}
    [IsSeparated B.hom] [T2Space (ComplexPoint W)] [T2Space (ComplexPoint E)]
    (β : W ⟶ B) (j : E ⟶ B) : T2Space (ComplexPoint (pullback β j)) := by
  letI : T2Space (ComplexPoint (W ⊗ E)) :=
    (HodgeLean.Foundations.complexPointProdHomeomorph W E).isEmbedding.t2Space
  letI := s2v_pullback_toProduct_closedImmersion β j
  exact (ComplexPoint.isEmbedding_map_of_closedImmersion
    (CartesianMonoidalCategory.lift (pullback.fst β j) (pullback.snd β j))).t2Space

theorem s2v_projective_preimage_projection_proper {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) :
    IsProperMap (s2c_points.map (s2b_toExceptional β j)) := by
  letI : CompactSpace (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_compact β j
  exact (Point.continuousMap (s2b_toExceptional β j)).continuous.isProperMap

end HodgeLean.Foundations.Program
