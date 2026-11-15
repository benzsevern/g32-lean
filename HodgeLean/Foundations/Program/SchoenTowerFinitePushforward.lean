import HodgeLean.Foundations.Program.SchoenTowerDiscreteSheaf
import HodgeLean.Foundations.Program.SchoenTowerFinitePointFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

theorem s2v_preimage_pushforward_shortExact {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0}
      (s2c_points.obj (s2b_preimage β j)))} (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (s2c_points.map (s2b_toExceptional β j)))).ShortExact := by
  letI : CompactSpace (s2c_points.obj (s2b_preimage β j)) := s2v_pullback_points_compact β j
  letI : T2Space (s2c_points.obj (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  apply s2v_proper_finiteFibres_pushforward_shortExact _
    (s2v_projective_preimage_projection_proper β j) ?_ hS
  intro y
  exact Set.finite_coe_iff.mp (s2v_preimage_point_fibre_finite β j y)

end HodgeLean.Foundations.Program
