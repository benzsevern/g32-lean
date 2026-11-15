import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneChains
import HodgeLean.Foundations.Program.SchoenTowerL1bActionCircleDegree
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalChains

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every equal subinterval of the n-turn loop is exactly one positive turn. -/
theorem s2v_l1b_action_winding_nat_restr (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    b3Rest2_restr (simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 n)))
      (b3Rest2_frac n j) (b3Rest2_frac n (j + 1)) =
    simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 1)) := by
  exact PuncturedPlane.winding_nat_restr n j hn hj

/-- Subdivision computes the natural winding coefficient in chains modulo
boundaries. -/
theorem s2v_l1b_action_winding_nat_chain (n : ℕ) :
    b6m_pathChain (simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 n))) =
      n • b6m_pathChain (simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 1))) := by
  exact PuncturedPlane.winding_nat_chain n

/-- Reversing a canonical winding path negates its integral number of turns. -/
theorem s2v_l1b_action_winding_neg_restr (k : ℤ) :
    b3Rest2_restr (simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 k))) 1 0 =
      simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 (-k))) := by
  exact PuncturedPlane.winding_neg_restr k

/-- Path subdivision at the two endpoints makes negative winding the additive
inverse in chains modulo boundaries. -/
theorem s2v_l1b_action_winding_neg_chain (k : ℤ) :
    b6m_pathChain (simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 (-k)))) =
      -b6m_pathChain (simplexPath (loopSimplex (s2v_l1b_action_windingCircleMap 0 k))) := by
  exact PuncturedPlane.winding_neg_chain k

/-- The canonical k-turn exponential loop represents k times the one-turn
loop in integral singular homology of the punctured plane. -/
theorem s2v_l1b_action_winding_loop_class (k : ℤ) :
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 k)) =
    k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)) := by
  exact PuncturedPlane.winding_loop_class k

end HodgeLean.Foundations.Program
