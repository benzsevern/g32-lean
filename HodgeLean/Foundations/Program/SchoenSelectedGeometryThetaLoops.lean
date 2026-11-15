import HodgeLean.Foundations.Program.SchoenSelectedGeometryThetaExponential
import HodgeLean.Adapters.DegreeOneLattice

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The selected theta map sends straight lattice loops to the corresponding algebraic period loops. -/
theorem s0_theta_lattice_loop
    (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F)
    (Q : LinearMap.BilinForm ℤ L) (hQ : b2_IsRiemannForm L F Q) :
    letI := b5_groupObj L F hF Q hQ
    letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
    letI := b5_smooth L F hF Q hQ
    letI := b5_projective L F hF Q hQ
    ∀ (l : L) (t : ℝ),
      b5_theta L F hF Q hQ (b2_torusCover L F ((t : ℂ) • b5_lattice L F l)) =
        abelianLatticeLoop (b5_model L F hF Q) (b5_periodEquiv L F hF Q hQ l) (t : UnitAddCircle) := by
  letI := b5_groupObj L F hF Q hQ
  letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
  letI := b5_smooth L F hF Q hQ
  letI := b5_projective L F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  intro l t
  rw [b56_cover_of _ _ (b5_theta_descent L F hF Q hQ), s0_theta_cover_exponential,
    map_smul]
  change (complexExponential (b5_model L F hF Q) _
      ((t : ℂ) • b5_periodDerivative L F hF Q hQ (b5_lattice L F l))).toMul =
    (oneParameterSubgroup (b5_model L F hF Q) _
      (b5_periodDerivative L F hF Q hQ (b5_lattice L F l)) t).toMul
  rw [Complex.coe_smul, complexExponential_smul]

#print axioms s0_theta_lattice_loop
end HodgeLean.Foundations.Program
