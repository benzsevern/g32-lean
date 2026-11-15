import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Pasting the two actual pullbacks identifies the covering slice with the original covering-point fibre of the composite base map. -/
def coveringSlicePointHomeomorph
    {W B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B) :
    ComplexPoint (coveringSlice β b x) ≃ₜ {w : ComplexPoint W // Point.map (β ≫ b) w = x} :=
  (Point.isoMapHomeomorph (pullbackRightPullbackFstIso b x β)).trans
    (s2v_separatedPointFibreHomeomorph (β ≫ b) x)

/-- The composite-fibre identification retains the original covering-point projection literally. -/
theorem coveringSlicePointHomeomorph_projection
    {W B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B)
    (z : ComplexPoint (coveringSlice β b x)) :
    (coveringSlicePointHomeomorph β b x z).val =
      Point.map (pullback.fst β (pullback.fst b x)) z := by
  change (s2v_separatedPointFibreHomeomorph (β ≫ b) x
    (Point.map (pullbackRightPullbackFstIso b x β).hom z)).val = _
  rw [s2v_separatedPointFibreHomeomorph_projection, ← Point.map_comp_apply,
    pullbackRightPullbackFstIso_hom_fst]

end AlgebraicGeometry.RamifiedNormalization.StageFour
