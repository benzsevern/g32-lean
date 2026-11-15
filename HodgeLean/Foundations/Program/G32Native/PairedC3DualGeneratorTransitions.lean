import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateGeneratorEvaluation

/-! # Original homogeneous ratios in the actual negative-line generators -/
noncomputable section
set_option maxHeartbeats 60000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- On the original overlap the negative-line generators change by the
original homogeneous ratio, with its original index order. -/
theorem paired_c3_coordinate_dual_generator_transition (k : ℕ) (i j : Fin (k + 1)) :
    (pairedC3NegativeLine k).presheaf.map (homOfLE
      (inf_le_left : ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j ≤ _)).op
        (pairedC3CoordinateDualGenerator k i) =
      (pairedC3Proj k).presheaf.map (homOfLE
        (inf_le_left : ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j ≤
          ProjSpace.standardOpen ℂ k i)).op
        (ProjSpace.coordinateRatioSection ℂ k i j) •
      (pairedC3NegativeLine k).presheaf.map (homOfLE
        (inf_le_right : ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j ≤
          ProjSpace.standardOpen ℂ k j)).op
        (pairedC3CoordinateDualGenerator k j) := by
  apply (paired_c3_coordinate_evaluation_bijective k j (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j) inf_le_right).injective
  change ((pairedC3CoordinateEvaluation k j).val.app (op (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j))).hom _ =
    ((pairedC3CoordinateEvaluation k j).val.app (op (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j))).hom (_ • _)
  rw [((pairedC3CoordinateEvaluation k j).val.app (op (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j))).hom.map_smul]
  have hi := PresheafOfModules.naturality_apply (pairedC3CoordinateEvaluation k j).val
    (homOfLE (show (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j) ≤ ProjSpace.standardOpen ℂ k i from inf_le_left)).op
      (pairedC3CoordinateDualGenerator k i)
  have hj := PresheafOfModules.naturality_apply (pairedC3CoordinateEvaluation k j).val
    (homOfLE (show (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j) ≤ ProjSpace.standardOpen ℂ k j from inf_le_right)).op
      (pairedC3CoordinateDualGenerator k j)
  change (pairedC3CoordinateEvaluation k j).app
    (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j) _ =
      (Scheme.Modules.presheaf (X := pairedC3Proj k)
        (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)).map
        (homOfLE (inf_le_left : ProjSpace.standardOpen ℂ k i ⊓
          ProjSpace.standardOpen ℂ k j ≤ ProjSpace.standardOpen ℂ k i)).op
        ((pairedC3CoordinateEvaluation k j).app (ProjSpace.standardOpen ℂ k i)
          (pairedC3CoordinateDualGenerator k i)) at hi
  change (pairedC3CoordinateEvaluation k j).app
    (ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j) _ =
      (Scheme.Modules.presheaf (X := pairedC3Proj k)
        (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)).map
        (homOfLE (inf_le_right : ProjSpace.standardOpen ℂ k i ⊓
          ProjSpace.standardOpen ℂ k j ≤ ProjSpace.standardOpen ℂ k j)).op
        ((pairedC3CoordinateEvaluation k j).app (ProjSpace.standardOpen ℂ k j)
          (pairedC3CoordinateDualGenerator k j)) at hj
  rw [paired_c3_coordinate_dual_generator_evaluation k i j] at hi
  rw [paired_c3_coordinate_dual_generator_evaluation k j j] at hj
  calc
    _ = (Scheme.Modules.presheaf (X := pairedC3Proj k)
        (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)).map
          (homOfLE (inf_le_left : ProjSpace.standardOpen ℂ k i ⊓
            ProjSpace.standardOpen ℂ k j ≤ ProjSpace.standardOpen ℂ k i)).op
          (ProjSpace.coordinateRatioSection ℂ k i j) := hi
    _ = (pairedC3Proj k).presheaf.map
        (homOfLE (inf_le_left : ProjSpace.standardOpen ℂ k i ⊓
          ProjSpace.standardOpen ℂ k j ≤ ProjSpace.standardOpen ℂ k i)).op
        (ProjSpace.coordinateRatioSection ℂ k i j) •
      (Scheme.Modules.presheaf (X := pairedC3Proj k)
        (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)).map
          (homOfLE (inf_le_right : ProjSpace.standardOpen ℂ k i ⊓
            ProjSpace.standardOpen ℂ k j ≤ ProjSpace.standardOpen ℂ k j)).op
          (ProjSpace.coordinateRatioSection ℂ k j j) := by
      change ((pairedC3Proj k).presheaf.map (homOfLE inf_le_left).op
          (ProjSpace.coordinateRatioSection ℂ k i j) :
            Γ(pairedC3Proj k, ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j)) =
        ((pairedC3Proj k).presheaf.map (homOfLE inf_le_left).op
            (ProjSpace.coordinateRatioSection ℂ k i j) *
          (pairedC3Proj k).presheaf.map (homOfLE inf_le_right).op
            (ProjSpace.coordinateRatioSection ℂ k j j) :
              Γ(pairedC3Proj k, ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j))
      rw [ProjSpace.coordinateRatioSection_self ℂ k j, map_one, mul_one]
    _ = _ := congrArg (fun z : Γ(SheafOfModules.unit (pairedC3Proj k).ringCatSheaf,
        ProjSpace.standardOpen ℂ k i ⊓ ProjSpace.standardOpen ℂ k j) =>
        (pairedC3Proj k).presheaf.map (homOfLE inf_le_left).op
          (ProjSpace.coordinateRatioSection ℂ k i j) • z) hj.symm

#print axioms paired_c3_coordinate_dual_generator_transition
end HodgeLean.Foundations.Program.G32Native
