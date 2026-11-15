import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveChartOpen
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedScaledSmooth

/-! # Smooth polynomial parameters in the projective target -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- A smooth affine-line parameter remains smooth after entering either
standard chart of the actual projective line. -/
theorem pairedC3_projective_parameter_smooth
    {B : Type} [CommRing B] [Algebra ℂ B] (i : Fin 2) (z : B)
    (h : Smooth (Spec.map (CommRingCat.ofHom
      (eval₂RingHom (algebraMap ℂ B) z)))) :
    Smooth (projectiveLineChart i z).left := by
  have he := pairedC3_projective_chart_restriction (aeval z) i (Polynomial.X : Polynomial ℂ)
  simp only [aeval_X] at he
  rw [← he]
  letI : Smooth (Spec.map (CommRingCat.ofHom (aeval z : Polynomial ℂ →ₐ[ℂ] B).toRingHom)) := h
  letI := pairedC3_projective_chart_open i
  infer_instance

#print axioms pairedC3_projective_parameter_smooth
end HodgeLean.Foundations.Program.G32Native
