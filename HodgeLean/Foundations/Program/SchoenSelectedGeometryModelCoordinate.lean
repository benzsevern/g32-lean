import HodgeLean.Foundations.Program.SchoenSelectedGeometryUnramifiedCoordinate
import HodgeLean.Foundations.Program.SchoenSelectedGeometryDimensionModel

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An ambient unramified algebraic coordinate supplies a finite flat local coordinate on the curve model.
Source: holomorphy of algebraic maps between smooth ambient schemes and the inverse function theorem. -/
theorem s0_model_finite_flat_local_coordinate
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [IsProjective Y.hom]
    (i : Y ⟶ X) (e : C ≃ₜ ComplexPoint Y)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω
      (fun z ↦ Point.map i (e z)))
    (r : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))) (x : C)
    (hd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun z ↦ s0_sphere_projective_homeomorph.symm (Point.map r (Point.map i (e z)))) x ≠ 0) :
    IsFinite (i ≫ r).left ∧ Flat (i ≫ r).left ∧ ∃ N : Set (ComplexPoint Y),
      IsOpen N ∧ e x ∈ N ∧ Set.InjOn (Point.map (i ≫ r)) N := by
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  letI : SmoothOfRelativeDimension 1 A.hom := s0_complex_projective_relative_dimension 1
  have hh : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z ↦ s0_sphere_projective_homeomorph.symm (Point.map r (Point.map i (e z)))) :=
    (s0_sphere_projective_inverse_holomorphic.comp
      (spec_contMDiff_pointMap_aux X A (TopologicalSpace.dim X.left) 1 r)).comp hf
  exact s0_finite_flat_locally_injective_coordinate Y (i ≫ r) e
    (by simpa only [Point.map_comp_apply] using hh) x
    (by simpa only [Point.map_comp_apply] using hd)

#print axioms s0_model_finite_flat_local_coordinate
end HodgeLean.Foundations.Program
