import HodgeLean.Foundations.Program.SchoenSelectedGeometryModelCoordinate

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The integral projective curve model has finite flat algebraic coordinates locally injective analytically.
Source: the projective analytic image construction and the unramified meromorphic coordinate family. -/
theorem s0_curve_model_with_finite_flat_local_coordinates
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (T : Finset (b4c_MeroFun ℂ C))
    (hsep : ∀ x y : C, (∀ F ∈ T, F x = F y) → x = y)
    (hder : ∀ x : C, ∃ F ∈ T, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x ≠ 0) :
    ∃ X : Over (Spec ↧ℂ),
      ∃ (_ : IsIntegral X.left) (_ : Smooth X.hom) (_ : IsProjective X.hom),
      ∃ Y : Over (Spec ↧ℂ), ∃ (_ : IsIntegral Y.left) (_ : IsProjective Y.hom),
        TopologicalSpace.dim Y.left = 1 ∧
        ∃ i : Y ⟶ X, IsClosedImmersion i.left ∧ ∃ e : C ≃ₜ ComplexPoint Y,
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω
            (fun x ↦ Point.map i (e x)) ∧
          ∀ x : C, ∃ q : Y ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)),
            IsFinite q.left ∧ Flat q.left ∧ ∃ N : Set (ComplexPoint Y),
              IsOpen N ∧ e x ∈ N ∧ Set.InjOn (Point.map q) N := by
  obtain ⟨X, hXi, hXs, hXp, Y, hYi, hYp, hd, i, hi, e, hf, hr⟩ :=
    s0_integral_dimension_one_model_of_sphere_coordinates T hsep hder
  letI := hXi
  letI := hXs
  letI := hYi
  letI := hYp
  refine ⟨X, hXi, hXs, hXp, Y, hYi, hYp, hd, i, hi, e, hf, ?_⟩
  intro x
  obtain ⟨r, hdr⟩ := hr x
  exact ⟨i ≫ r, s0_model_finite_flat_local_coordinate X Y i e hf r x hdr⟩

#print axioms s0_curve_model_with_finite_flat_local_coordinates
end HodgeLean.Foundations.Program
