import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- On the actual exceptional point slice, the affine-neighbourhood part of the first chart image is automatic, leaving exactly the second-support complement. -/
theorem slice_chart_image_complement
    {W X B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (β : W ⟶ X) (b : X ⟶ B) (x : ComplexPoint B)
    (U : B.left.Opens) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ U)
    {A : Scheme} (j : A ⟶ X.left) (D : X.left.IdealSheafData)
    (hrange : Set.range j = (b.left ⁻¹ᵁ U : Set X.left) \ D.support)
    (z : ComplexPoint (coveringSlice β b x)) :
    (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
      (IsLocalRing.closedPoint ℂ) ∈ Set.range j ↔
    (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
      (IsLocalRing.closedPoint ℂ) ∉ D.support := by
  let q := Point.map (sliceProjection β b x) z
  have hpoint := (s2v_separatedPointFibreHomeomorph b x q).property
  change Point.map b (Point.map (pullback.fst b x) q) = x at hpoint
  have hbase := congrArg (fun y : ComplexPoint B => y.left (IsLocalRing.closedPoint ℂ)) hpoint
  have hU : (Point.map (pullback.fst b x) q).left (IsLocalRing.closedPoint ℂ) ∈ b.left ⁻¹ᵁ U := by
    change b.left ((Point.map (pullback.fst b x) q).left (IsLocalRing.closedPoint ℂ)) ∈ U
    change b.left ((Point.map (pullback.fst b x) q).left (IsLocalRing.closedPoint ℂ)) = _ at hbase
    rw [hbase]
    exact hx
  rw [hrange]
  exact and_iff_right hU

end AlgebraicGeometry.RamifiedNormalization.StageFour
