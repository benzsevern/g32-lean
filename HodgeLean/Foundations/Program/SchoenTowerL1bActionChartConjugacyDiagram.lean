import HodgeLean.Foundations.Program.SchoenTowerL1bActionVectorConjugacy
import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartDiskCoordinates

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The actual disk-to-manifold pair maps commute with the supplied
homeomorphism, using its centered coordinate representative. -/
theorem s2v_l1b_action_chart_conjugacy_pair_diagram
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (d : OpenPartialHomeomorph N (Fin 1 → ℂ)) (E : M ≃ₜ N) (x : M) (r : ℝ)
    (hb : Metric.ball (0 : ℂ) r ⊆ (s2v_l1b_action_vectorConjugacy e d E x).source)
    (hc : ContinuousOn (s2v_l1b_action_vectorConjugacy e d E x) (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 →
      s2v_l1b_action_vectorConjugacy e d E x z ≠ 0)
    (hs : ∀ z ∈ Metric.ball (0 : ℂ) r, b6m_surfaceCoordinateEquiv z + e x ∈ e.target)
    (ht : ∀ z ∈ Metric.ball (0 : ℂ) r,
      b6m_surfaceCoordinateEquiv (s2v_l1b_action_vectorConjugacy e d E x z) + d (E x) ∈ d.target) :
    s2v_l1b_action_chart_disk_coordinates d (E x)
        (s2v_l1b_action_vectorConjugacy e d E x) r hc hn ht ≫
      chartTargetInverseAtSourcePairMap 1 d (E x) =
    (s2v_l1b_action_chart_disk_coordinates e x (fun z => z) r continuous_id.continuousOn
        (fun _ _ h => h) hs ≫ chartTargetInverseAtSourcePairMap 1 e x) ≫
      imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    exact s2v_l1b_action_vectorConjugacy_inverse_diagram e d E x z.val.val (hb z.val.property)
  · ext z
    exact s2v_l1b_action_vectorConjugacy_inverse_diagram e d E x z.val (hb z.property)

end HodgeLean.Foundations.Program
