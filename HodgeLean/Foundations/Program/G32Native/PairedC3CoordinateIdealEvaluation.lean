import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateRestrictionZero
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateEvaluationRatio
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateDualGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3DualEvaluationFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3FrameCoverMorphisms

/-! # Coordinate evaluation factors through the actual hyperplane ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A module map from the structure module kills every multiple of an element it kills. -/
theorem paired_c3_unit_map_product_zero {X : Scheme.{0}} {N : X.Modules}
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ N) (U : X.Opens)
    (r c : Γ(X, U)) (h : Scheme.Modules.Hom.app (X := X) q U r = 0) :
    Scheme.Modules.Hom.app (X := X) q U (r * c) = 0 := by
  rw [mul_comm]
  change (q.val.app (Opposite.op U)).hom (c • r) = 0
  rw [map_smul]
  change (q.val.app (Opposite.op U)).hom r = 0 at h
  exact (congrArg (fun z : Γ(N, U) => c • z) h).trans (smul_zero c)

/-- The original coordinate evaluation vanishes under hyperplane restriction. -/
theorem paired_c3_coordinate_evaluation_restriction_zero (k : ℕ) (j : Fin (k + 1)) :
    pairedC3CoordinateEvaluation k j ≫ SheafOfModules.unitToPushforwardObjUnit
      (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom = 0 := by
  apply paired_c3_hom_zero_of_frame_cover
    (fun i : ULift (Fin (k + 1)) => ProjSpace.standardOpen ℂ k i.down)
    (ProjSpace.stdCover ℂ k).iSup_eq_top (fun i => pairedC3CoordinateDualGenerator k i.down)
    (fun i => paired_c3_coordinate_dual_generator_frame k i.down)
  intro idx
  let i := idx.down
  change Scheme.Modules.Hom.app (X := pairedC3Proj k)
    (SheafOfModules.unitToPushforwardObjUnit
      (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom) _
    ((pairedC3CoordinateEvaluation k j).app _ (pairedC3CoordinateDualGenerator k i)) = 0
  rw [paired_c3_coordinate_evaluation_ratio]
  change Scheme.Modules.Hom.app (X := pairedC3Proj k)
    (SheafOfModules.unitToPushforwardObjUnit
      (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom)
    (ProjSpace.standardOpen ℂ k i)
    (ProjSpace.coordinateRatioSection ℂ k i j *
      (show Γ(pairedC3Proj k, ProjSpace.standardOpen ℂ k i) from
        (pairedC3CoordinateEvaluation k i).app _ (pairedC3CoordinateDualGenerator k i))) = 0
  exact paired_c3_unit_map_product_zero _ _ _ _
    (paired_c3_coordinate_ratio_restriction_zero k i j)

/-- Evaluation with its original scale, into the actual categorical ideal kernel. -/
def pairedC3CoordinateIdealEvaluation (k : ℕ) (j : Fin (k + 1)) :
    pairedC3NegativeLine k ⟶
      Conormal.idealModule (pairedC3CoordinateHyperplaneIdeal k j).subschemeι :=
  kernel.lift _ (pairedC3CoordinateEvaluation k j)
    (paired_c3_coordinate_evaluation_restriction_zero k j)

/-- Inclusion retains exactly the original evaluation arrow. -/
theorem paired_c3_coordinate_ideal_evaluation_inclusion (k : ℕ) (j : Fin (k + 1)) :
    pairedC3CoordinateIdealEvaluation k j ≫ kernel.ι
      (SheafOfModules.unitToPushforwardObjUnit
        (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom) =
      pairedC3CoordinateEvaluation k j := kernel.lift_ι _ _ _

#print axioms paired_c3_unit_map_product_zero
#print axioms paired_c3_coordinate_evaluation_restriction_zero
#print axioms pairedC3CoordinateIdealEvaluation
#print axioms paired_c3_coordinate_ideal_evaluation_inclusion
end HodgeLean.Foundations.Program.G32Native
