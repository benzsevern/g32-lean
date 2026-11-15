import HodgeLean.Foundations.Program.SchoenSelectedGeometryCoordinateDimension

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A compact analytic curve image with a nonconstant algebraic sphere coordinate has an
integral projective model of dimension one.
Source: Chow's theorem, the analytic identity principle, and the finite-coordinate dimension bound. -/
theorem s0_curve_model_of_analytic_image
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (f : C → ComplexPoint A) (he : IsClosedEmbedding f)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim A.left) → ℂ) ω f)
    (ha : IsClosedAnalytic (Fin (TopologicalSpace.dim A.left) → ℂ) (range f))
    (q : A ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    (hq : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (f x))))
    (hnc : ∃ x y : C, Point.map q (f x) ≠ Point.map q (f y)) :
    ∃ Y : Over (Spec ↧ℂ), ∃ (_ : IsIntegral Y.left) (_ : IsProjective Y.hom),
      TopologicalSpace.dim Y.left = 1 ∧
      ∃ i : Y ⟶ A, IsClosedImmersion i.left ∧ ∃ e : C ≃ₜ ComplexPoint Y,
        ∀ x, Point.map i (e x) = f x := by
  obtain ⟨Z, hZ, hcar⟩ := chowG_setLevel A (range f) ha
  have hir : IsIrreducible Z := by
    rw [s0_carrier_eq_closure_range A f Z hZ hcar]
    exact (s0_holomorphic_image_irreducible A f hf).closure
  obtain ⟨Y, hYr, hYp, i, hi, hri, e, heq⟩ :=
    s0_reduced_model_of_projective_carrier A f he Z hZ hcar
  letI := hYr
  letI := hYp
  letI := hi
  letI : IsIntegral Y.left := s0_integral_of_reduced_closed_image i.left (by rw [hri]; exact hir)
  have hcomp (x : C) : Point.map (i ≫ q) (e x) = Point.map q (f x) := by
    rw [Point.map_comp_apply, heq]
  have hd := s0_model_dimension_of_nonconstant_coordinate Y (i ≫ q) e
    (by simpa only [hcomp] using hq) (by simpa only [hcomp] using hnc)
  exact ⟨Y, inferInstance, hYp, hd, i, hi, e, heq⟩

#print axioms s0_curve_model_of_analytic_image
end HodgeLean.Foundations.Program
