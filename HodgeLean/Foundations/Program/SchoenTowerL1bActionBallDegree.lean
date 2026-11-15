import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneBall
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNeighbourhoodDegree

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The positive circular loop of radius ρ inside a punctured disk of radius r. -/
def s2v_l1b_action_ball_loop (r ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    C(UnitAddCircle, (neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0).snd) := by
  let w := s2v_l1b_action_windingCircleMap (ρ.log : ℂ) 1
  have hn (t : UnitAddCircle) : (w t).val ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, s2v_l1b_action_windingCircleMap_norm]
    change Real.exp (Real.log ρ) < r
    rwa [Real.exp_log hρ]
  exact ⟨fun t => ⟨⟨(w t).val, hn t⟩, (w t).property⟩,
    ((continuous_subtype_val.comp w.continuous).subtype_mk hn).subtype_mk _⟩

/-- Inclusion of the disk loop is the canonical winding circle in the plane. -/
theorem s2v_l1b_action_ball_loop_inclusion (r ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0).left.hom.comp
      (s2v_l1b_action_ball_loop r ρ hρ hρr) =
    s2v_l1b_action_windingCircleMap (ρ.log : ℂ) 1 := rfl

/-- The included positive disk loop is the integral one-turn generator in
the punctured plane. -/
theorem s2v_l1b_action_ball_loop_homology (r ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    homologyMap ℤ 1 (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0).left
      (((SingularChainComplex ℤ
        (neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0).snd).sc 1).moduleCatHomologyClass
          (loopCycle ℤ (s2v_l1b_action_ball_loop r ρ hρ hρr))) =
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)) := by
  have h := b6m_homologyMap_loopCycle
    (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0).left.hom
    (s2v_l1b_action_ball_loop r ρ hρ hρr)
  rw [s2v_l1b_action_ball_loop_inclusion] at h
  apply h.trans
  have hh := s2v_l1b_action_winding_circle_class (ρ.log : ℂ) 1
  rw [one_smul] at hh
  exact hh

/-- Inclusion of a positive-radius disk induces an integral H₁ isomorphism
on the punctured complements. -/
theorem s2v_l1b_action_ball_homology_bijective (r : ℝ) (hr : 0 < r) :
    Function.Bijective (homologyMap ℤ 1
      (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0).left) := by
  exact PuncturedPlane.ballInclusion_of_positive r hr

end HodgeLean.Foundations.Program
