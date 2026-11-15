import HodgeLean.Adapters.GagaMaps
import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteEmbedding
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLocalCoordinateModel
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveLineSmooth
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySmoothComparison
import HodgeLean.Foundations.Program.SchoenSelectedGeometryNonisolated

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Algebraize the image of finite meromorphic coordinates separating points and tangent lines.
Source: Chow, On compact complex analytic varieties, Amer. J. Math. 71 (1949), 893–914. -/
theorem s0_projective_model_of_sphere_coordinates (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (T : Finset (b4c_MeroFun ℂ C))
    (hsep : ∀ x y : C, (∀ F ∈ T, F x = F y) → x = y)
    (hder : ∀ x : C, ∃ F ∈ T,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x ≠ 0) :
    ∃ X : Over (Spec ↧ℂ),
      ∃ (_ : IsIntegral X.left) (_ : Smooth X.hom) (_ : IsProjective X.hom),
      TopologicalSpace.dim X.left = 1 ∧
      ∃ e : C ≃ₜ ComplexPoint X,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω e ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm := by
  obtain ⟨X, hXi, hXs, hXp, Y, hYi, hYp, hd, i, hi, e, hf, hr⟩ :=
    s0_curve_model_with_finite_flat_local_coordinates T hsep hder
  letI := hXi
  letI := hXs
  letI := hYi
  letI := hYp
  have hYs : Smooth Y.hom := by
    apply s0_smooth_of_complex_points Y
    intro z
    obtain ⟨q, hqf, hqflat, N, hN, hz, hinj⟩ := hr (e.symm z)
    letI := hqf
    letI := hqflat
    letI := s0_curve_model_punctured_neBot e z
    exact s0_finite_flat_projective_line_smooth_at Y q z N hN
      (by simpa only [e.apply_symm_apply] using hz) hinj
  letI := hYs
  letI := hi
  obtain ⟨he, hei⟩ := s0_biholomorphic_of_smooth_curve_ambient_comparison X Y hd i e hf
  exact ⟨Y, hYi, hYs, hYp, hd, e, he, hei⟩

/-- A compact connected Riemann surface has a smooth projective curve model.
Source: Forster, Lectures on Riemann Surfaces, GTM 81, §30. -/
theorem s0_curve_model_exists (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ X : Over (Spec ↧ℂ),
      ∃ (_ : IsIntegral X.left) (_ : Smooth X.hom) (_ : IsProjective X.hom),
      TopologicalSpace.dim X.left = 1 ∧
      ∃ e : C ≃ₜ ComplexPoint X,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω e ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm := by
  obtain ⟨T, hsep, hder⟩ := s0_finite_meromorphic_immersion (C := C)
  exact s0_projective_model_of_sphere_coordinates C T hsep hder

#print axioms s0_projective_model_of_sphere_coordinates
#print axioms s0_curve_model_exists

theorem s0_curve_model_map
    {C D : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [TopologicalSpace D] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω D]
    (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (eC : C ≃ₜ ComplexPoint X) (eD : D ≃ₜ ComplexPoint Y)
    (hC : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω eC.symm)
    (hD : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y.left) → ℂ) ω eD)
    (F : C → D) (hF : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F) :
    ∃ f : X ⟶ Y, ∀ x, Point.map f (eC x) = eD (F x) := by
  obtain ⟨f, hf⟩ := HodgeLean.Adapters.gagam_algebraize X Y
    (fun x ↦ eD (F (eC.symm x))) (hD.comp (hF.comp hC))
  refine ⟨f, fun x ↦ ?_⟩
  rw [hf]
  change eD (F (eC.symm (eC x))) = eD (F x)
  rw [eC.symm_apply_apply]

#print axioms s0_curve_model_map

end HodgeLean.Foundations.Program
