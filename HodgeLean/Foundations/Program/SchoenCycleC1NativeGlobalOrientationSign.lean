import HodgeLean.Foundations.Program.SchoenCycleC1GlobalOrientationSign
import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeChartSign
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The original surface homeomorphism has one sign on every specified
native integral curve class. Compactness and connectedness of the source
are transported from the actual integral projective complex curve. -/
theorem s2e_c1_native_global_orientation_sign
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] (eY : M ≃ₜ ComplexPoint Y) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x : M,
      relativeHomologyMap ℤ 2
        (imagePointPairMap (TopCat.ofHom ⟨eY, eY.continuous⟩) eY.injective x)
        (b6m_surfaceLocalClass ℤ x) =
          ε • s2v_l1b_action_curveLocalClass Y hdimY (eY x) := by
  letI : ConnectedSpace (ComplexPoint Y) := ComplexPoint.connectedSpace Y
  letI : T2Space M := eY.symm.t2Space
  letI : CompactSpace M := eY.symm.compactSpace
  letI : ConnectedSpace M := eY.symm.surjective.connectedSpace eY.symm.continuous
  obtain ⟨ε, hε, he⟩ := s2e_c1_homeomorphism_global_orientation_sign eY
  refine ⟨ε, hε, fun x => ?_⟩
  have hclass := s2v_l1b_action_curve_class_native_chart Y hdimY (eY x)
  exact (he x).trans (congrArg (fun a => ε • a) hclass.symm)

end HodgeLean.Foundations.Program
