import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cComplexOrientation
import HodgeLean.Foundations.Program.SchoenTowerL1bActionBoundary

/-! Punctured disk inclusion on integral first homology.
Source: Hatcher, Algebraic Topology (2002), §§2.1–2.2.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Foundations.Program
namespace AlgebraicTopology.Singular.PuncturedPlane

theorem ballInclusion_of_positive (r : ℝ) (hr : 0 < r) :
    Function.Bijective (homologyMap ℤ 1
      (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0).left) := by
  letI : ContractibleSpace (neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0).fst := by
    change ContractibleSpace (Metric.ball (0 : ℂ) r)
    exact (convex_ball (0 : ℂ) r).contractibleSpace ⟨0, Metric.mem_ball_self hr⟩
  letI : ContractibleSpace (pointComplementPair (0 : ℂ)).fst := by
    change ContractibleSpace ℂ
    infer_instance
  apply s2v_l1b_action_boundary_homology_bijective ℤ
  exact b6m_point_excision_bijective ℤ (Metric.ball (0 : ℂ) r) 0
    Metric.isOpen_ball (Metric.mem_ball_self hr) 2

end AlgebraicTopology.Singular.PuncturedPlane
