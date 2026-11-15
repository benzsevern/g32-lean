import HodgeLean.Foundations.Program.SchoenTowerL1bActionCenteredConjugacy
import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplitDefs

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The native one-dimensional chart expressed as a scalar complex chart. -/
def s2v_l1b_action_nativePlaneChart
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) : OpenPartialHomeomorph (ComplexPoint Y) ℂ :=
  (ComplexPoint.localChart Y 1 p).trans
    b6m_surfaceCoordinateEquiv.symm.toHomeomorph.toOpenPartialHomeomorph

/-- The scalar native chart contains the marked point. -/
theorem s2v_l1b_action_nativePlaneChart_source
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) : p ∈ (s2v_l1b_action_nativePlaneChart Y p).source :=
  ⟨ComplexPoint.mem_localChart_source Y 1 p, Set.mem_univ _⟩

/-- Evaluation of the scalar native chart is evaluation at its sole index. -/
theorem s2v_l1b_action_nativePlaneChart_apply
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p q : ComplexPoint Y) :
    s2v_l1b_action_nativePlaneChart Y p q = ComplexPoint.localChart Y 1 p q 0 := rfl

/-- The actual centered coordinate representative of the supplied surface
homeomorphism into the native curve. -/
def s2v_l1b_action_nativeConjugacy
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) : OpenPartialHomeomorph ℂ ℂ :=
  s2v_l1b_action_centeredConjugacy (chartAt ℂ x)
    (s2v_l1b_action_nativePlaneChart Y (E x)) E x

/-- The supplied homeomorphism has a continuous centered representative
on some genuine disk, nonzero on the punctured disk. -/
theorem s2v_l1b_action_nativeConjugacy_disk
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆
      (s2v_l1b_action_nativeConjugacy Y E x).source ∧
      ContinuousOn (s2v_l1b_action_nativeConjugacy Y E x) (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 →
        s2v_l1b_action_nativeConjugacy Y E x z ≠ 0 := by
  exact s2v_l1b_action_centered_partial_disk _
    (s2v_l1b_action_centeredConjugacy_source _ _ E x (mem_chart_source ℂ x)
      (s2v_l1b_action_nativePlaneChart_source Y (E x)))
    (s2v_l1b_action_centeredConjugacy_zero _ _ E x (mem_chart_source ℂ x))

/-- The representative evaluates the given homeomorphism between the
centered preferred source chart and the scalar native target chart. -/
theorem s2v_l1b_action_nativeConjugacy_apply
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) (z : ℂ) :
    s2v_l1b_action_nativeConjugacy Y E x z =
      ComplexPoint.localChart Y 1 (E x)
        (E ((chartAt ℂ x).symm (z + chartAt ℂ x x))) 0 -
          ComplexPoint.localChart Y 1 (E x) (E x) 0 := rfl

end HodgeLean.Foundations.Program
