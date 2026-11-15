import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartDiskCoordinates

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A disk coordinate map with scalar multiplicity k transports its class
to k times the exact chart-local class. -/
theorem s2v_l1b_action_chart_disk_class
    (R : Type) [CommRing R] {M : Type} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ)) (x : M) (hx : x ∈ e.source)
    (h : ℂ → ℂ) (r : ℝ) (hc : ContinuousOn h (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → h z ≠ 0)
    (ht : ∀ z ∈ Metric.ball (0 : ℂ) r, b6m_surfaceCoordinateEquiv (h z) + e x ∈ e.target)
    (a : RelativeHomology R (neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0) 2)
    (k : ℤ) (ha : relativeHomologyMap R 2 (s2v_l1b_action_disk_pair_map h r hc hn) a =
      k • s2v_l1b_action_scalarLocalClass R) :
    relativeHomologyMap R 2
      (s2v_l1b_action_chart_disk_coordinates e x h r hc hn ht ≫
        chartTargetInverseAtSourcePairMap 1 e x) a =
      k • b6m_localClassOfChart R 1 e x hx := by
  apply s2v_l1b_action_chart_inverse_class_smul R 1 e x hx _ _ a k
  rw [s2v_l1b_action_chart_disk_coordinates_factorization]
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply, ha, map_zsmul]
  exact congrArg (fun c => k • relativeHomologyMap R 2
    (translationPointComplementPairMap (Fin 1 → ℂ) (e x)) c)
      (s2v_l1b_action_scalarLocalClass_normalization R)

end HodgeLean.Foundations.Program
