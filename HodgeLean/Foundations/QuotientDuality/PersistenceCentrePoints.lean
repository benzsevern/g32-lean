import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import HodgeLean.Foundations.QuotientDuality.PersistenceSupport
import HodgeLean.Foundations.Program.SchoenCycleBranchImagePoints

/-! The actual complex points of a scheme centre. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_subscheme_point_range
    (B : Over (Spec ↧ℂ)) [LocallyOfFiniteType B.hom]
    (I : B.left.IdealSheafData) :
    Set.range (Point.map (s2c_subschemeι B I)) =
      Point.underlying ⁻¹' (I.support : Set B.left) := by
  haveI : LocallyOfFiniteType (s2c_subscheme B I).hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change (Point.map (s2c_subschemeι B I) z).underlying ∈ I.support
    rw [Point.underlying_map]
    change I.subschemeι z.underlying ∈ (I.support : Set B.left)
    rw [← I.range_subschemeι]
    exact ⟨z.underlying, rfl⟩
  · intro hy
    apply s2e_complexPoint_lift_of_mem_range (s2c_subschemeι B I) y
    change y.underlying ∈ Set.range I.subschemeι
    rw [I.range_subschemeι]
    exact hy

lemma persistence_preimage_point_range_isClosed
    {W B K : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : K ⟶ B)
    [IsClosedImmersion j.left] :
    IsClosed (Set.range (Point.map (s2b_toCover β j))) := by
  haveI : IsClosedImmersion (s2b_toCover β j).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (((IsPullback.of_hasPullback β j).map (Over.forget _)).flip)
      (inferInstance : IsClosedImmersion j.left)
  exact (ComplexPoint.isClosedEmbedding_map_of_closedImmersion
    (s2b_toCover β j)).isClosed_range

end HodgeLean.Foundations.QuotientDuality
