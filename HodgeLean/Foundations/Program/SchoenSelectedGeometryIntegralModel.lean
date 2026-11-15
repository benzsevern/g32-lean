import HodgeLean.Foundations.Program.SchoenSelectedGeometryReducedModel
import HodgeLean.Foundations.Program.SchoenSelectedGeometryIntegralImage
import HodgeLean.Foundations.Program.SchoenSelectedGeometryImageIrreducible
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCarrierClosure

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Finite separating unramified meromorphic coordinates give an integral projective model,
with a homeomorphic comparison whose composite into a smooth ambient scheme is holomorphic.
Source: Chow's theorem, the analytic identity principle, and the reduced induced subscheme. -/
theorem s0_integral_projective_model_of_sphere_coordinates
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (T : Finset (b4c_MeroFun ℂ C))
    (hsep : ∀ x y : C, (∀ F ∈ T, F x = F y) → x = y)
    (hder : ∀ x : C, ∃ F ∈ T, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x ≠ 0) :
    ∃ A : Over (Spec ↧ℂ),
      ∃ (_ : IsIntegral A.left) (_ : Smooth A.hom) (_ : IsProjective A.hom),
      ∃ Y : Over (Spec ↧ℂ), ∃ (_ : IsIntegral Y.left) (_ : IsProjective Y.hom),
        ∃ i : Y ⟶ A, IsClosedImmersion i.left ∧ ∃ e : C ≃ₜ ComplexPoint Y,
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim A.left) → ℂ) ω
            (fun x ↦ Point.map i (e x)) := by
  obtain ⟨A, hAi, hAs, hAp, f, Z, he, hf, hZ, hcar⟩ :=
    s0_projective_carrier_of_sphere_coordinates T hsep hder
  letI := hAi
  letI := hAs
  letI := hAp
  have hir : IsIrreducible Z := by
    rw [s0_carrier_eq_closure_range A f Z hZ hcar]
    exact (s0_holomorphic_image_irreducible A f hf).closure
  obtain ⟨Y, hYr, hYp, i, hi, hri, e, heq⟩ :=
    s0_reduced_model_of_projective_carrier A f he Z hZ hcar
  letI := hYr
  letI := hYp
  letI := hi
  have hYi : IsIntegral Y.left := s0_integral_of_reduced_closed_image i.left (by rw [hri]; exact hir)
  refine ⟨A, hAi, hAs, hAp, Y, hYi, hYp, i, hi, e, ?_⟩
  simpa only [heq] using hf

#print axioms s0_integral_projective_model_of_sphere_coordinates
end HodgeLean.Foundations.Program
