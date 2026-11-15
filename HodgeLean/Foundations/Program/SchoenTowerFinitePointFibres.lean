import HodgeLean.Foundations.Program.SchoenTowerPullbackTopology
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_finite_complexPoint_fibre {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) [IsFinite f.left]
    (y : ComplexPoint Y) : Finite {x : ComplexPoint X // Point.map f x = y} := by
  letI := (f.left.finite_preimage_singleton y.underlying).to_subtype
  let g : {x : ComplexPoint X // Point.map f x = y} →
      ↥(f.left ⁻¹' {y.underlying}) := fun x => ⟨x.val.underlying, by
        change f.left x.val.underlying = y.underlying
        rw [← Point.underlying_map, x.property]⟩
  apply Finite.of_injective g
  intro x z hxz
  apply Subtype.ext
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  exact congrArg Subtype.val hxz

theorem s2v_preimage_projection_finite {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) :
    IsFinite (s2b_toExceptional β j).left := by
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    ((IsPullback.of_hasPullback β j).map (Over.forget _))
    (show IsFinite β.left from inferInstance)

theorem s2v_preimage_point_fibre_finite {W B E : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType E.hom] (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (y : ComplexPoint E) :
    Finite {x : ComplexPoint (s2b_preimage β j) //
      Point.map (s2b_toExceptional β j) x = y} := by
  letI := s2v_preimage_projection_finite β j
  letI : LocallyOfFiniteType (s2b_preimage β j).hom := by
    rw [← (s2b_toExceptional β j).w]
    infer_instance
  exact s2v_finite_complexPoint_fibre (s2b_toExceptional β j) y

end HodgeLean.Foundations.Program
