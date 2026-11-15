import HodgeLean.Foundations.Program.SchoenCycleC1ActualLocalActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1DvrEigenorderHelpers
import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter
import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation

/-! # Signed orders of actual curve rational eigenfunctions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An actual smooth curve automorphism fixing the point supplies the signed
order and native parameter multiplier of every nonzero rational eigenfunction. -/
theorem s2e_c1_actual_curve_rational_eigenorder
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (f : X ⟶ X) [IsIso f.left] (p : ComplexPoint X)
    (hp : f.left p.underlying = p.underlying)
    (z : X.left.functionField) (hz : z ≠ 0) (η : ℂ)
    (heig : s2e_step1_fieldPullback X.left f.left z =
      HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) η * z) :
    let R := X.left.presheaf.stalk p.underlying
    let t := s2e_native_curve_parameter X p
    ∃ (v u : Rˣ) (n : ℤ),
      s2e_fixed_point_stalkPullback X.left f.left p.underlying hp t = t * (v : R) ∧
      z = algebraMap R X.left.functionField (u : R) * algebraMap R X.left.functionField t ^ n ∧
      p.stalkHom.hom (v : R) ^ n = η := by
  let R := X.left.presheaf.stalk p.underlying
  let t := s2e_native_curve_parameter X p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  letI := HodgeLean.Foundations.Curves.functionFieldAlgebra X
  haveI : IsScalarTower ℂ R X.left.functionField := s2e_c1_actual_stalk_field_scalar_tower X p.underlying
  haveI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr X p
  have ht : Irreducible t := s2e_native_curve_parameter_irreducible X p
  obtain ⟨τ, hτ⟩ := s2e_c1_fixed_point_stalk_algEquiv X f p.underlying hp
  obtain ⟨σ, hσ⟩ := s2e_c1_actual_fieldPullback_algEquiv X f
  have hcompat (r : R) : σ (algebraMap R X.left.functionField r) =
      algebraMap R X.left.functionField (τ r) := by
    change σ.toRingHom _ = algebraMap R X.left.functionField (τ.toRingHom r)
    rw [hσ, hτ]
    exact s2e_c1_fieldPullback_local_stalk X.left f.left p.underlying hp r
  have he : σ z = algebraMap ℂ X.left.functionField η * z := by
    change σ.toRingHom z = _
    rw [hσ]
    exact heig
  obtain ⟨v, u, n, hv, hu, hn⟩ := s2e_c1_dvr_rational_eigenorder_character
    (s2e_complex_point_augmentation X p) τ σ hcompat t ht z hz η he
  refine ⟨v, u, n, ?_, hu, hn⟩
  change τ.toRingHom t = t * (v : R) at hv
  rwa [hτ] at hv

end HodgeLean.Foundations.Program
