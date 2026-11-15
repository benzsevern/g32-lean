import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs
import HodgeLean.Foundations.Program.SchoenTowerPullbackTopology
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual covering-slice projection is proper whenever the original covering and successor base have compact complex point spaces. -/
theorem covering_slice_projection_proper
    {W B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom] [IsSeparated B'.hom]
    [CompactSpace (ComplexPoint W)] [CompactSpace (ComplexPoint B')]
    [T2Space (ComplexPoint B')]
    (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B) :
    IsProperMap (Point.map (sliceProjection β b x)) := by
  letI : CompactSpace (ComplexPoint (exceptionalSlice b x)) := s2v_schemeFibre_compact b x
  let H := s2v_separatedPointFibreHomeomorph b x
  letI : T2Space (ComplexPoint (exceptionalSlice b x)) := H.isEmbedding.t2Space
  letI : CompactSpace (ComplexPoint (coveringSlice β b x)) :=
    s2v_pullback_points_compact β (CategoryTheory.Limits.pullback.fst b x)
  exact (Point.continuousMap (sliceProjection β b x)).continuous.isProperMap

end AlgebraicGeometry.RamifiedNormalization.StageFour
