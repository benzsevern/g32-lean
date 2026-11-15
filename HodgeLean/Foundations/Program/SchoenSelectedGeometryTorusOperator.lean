import HodgeLean.Foundations.Program.SchoenSelectedGeometryThetaExponential
import HodgeLean.Adapters.DegreeOneLattice
import HodgeLean.Foundations.Program.SchoenSelectedGeometryThetaLoops
import HodgeLean.Foundations.Program.SchoenSelectedGeometryTorusLines
import HodgeLean.Foundations.Program.G32SelectedRealizationImage

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A continuous map compatible with the theta identification induces the selected lattice operator. -/
theorem s0_model_torus_operator
    (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F)
    (Q : LinearMap.BilinForm ℤ L) (hQ : b2_IsRiemannForm L F Q)
    (φ : L →+ L) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj L F hF Q hQ
    letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
    letI := b5_smooth L F hF Q hQ
    letI := b5_projective L F hF Q hQ
    ∀ (k : ContinuousMap (ComplexPoint (b5_model L F hF Q)) (ComplexPoint (b5_model L F hF Q)))
      (_ : ∀ z, k (b5_theta L F hF Q hQ z) = b5_theta L F hF Q hQ (b2_torusHom F F φ hφ z))
      (x : HodgeLean.RealDefs.HQ (b5_model L F hF Q) 1),
      (cupComparison (b5_model L F hF Q) 1).symm
        (AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom k)
          (cupComparison (b5_model L F hF Q) 1 x)) = b63g_modelOperator L F hF Q hQ φ x := by
  letI := b5_groupObj L F hF Q hQ
  letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
  letI := b5_smooth L F hF Q hQ
  letI := b5_projective L F hF Q hQ
  intro k hk x
  have hloop (l : L) : k.comp (abelianLatticeLoop (b5_model L F hF Q) (b5_periodEquiv L F hF Q hQ l)) =
      abelianLatticeLoop (b5_model L F hF Q) (b5_periodEquiv L F hF Q hQ (φ l)) := by
    ext z : 1
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      change k (abelianLatticeLoop _ _ (t : UnitAddCircle)) = abelianLatticeLoop _ _ (t : UnitAddCircle)
      rw [← s0_theta_lattice_loop, ← s0_theta_lattice_loop, hk, s0_torus_lattice_line_map]
  apply (abelianPeriodEquiv (b5_model L F hF Q)).injective
  ext l
  obtain ⟨v, rfl⟩ := (b5_periodEquiv L F hF Q hQ).surjective l
  rw [g32x_modelOperator_period]
  have hp := Classical.choose_spec (spec_abelianPeriod_equiv (b5_model L F hF Q))
  simp only [abelianPeriodEquiv, hp]
  change loopPeriod (abelianLatticeLoop _ _) ((cupComparison _ 1)
    ((cupComparison _ 1).symm _)) = loopPeriod (abelianLatticeLoop _ _) (cupComparison _ 1 x)
  rw [LinearEquiv.apply_symm_apply, ← loopPeriod_comp, hloop]

#print axioms s0_model_torus_operator
end HodgeLean.Foundations.Program
