import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteCoordinate
import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexDominance
import HodgeLean.Foundations.Program.SchoenSelectedGeometryFlatCurve
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLineStalks

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A nonconstant holomorphic sphere coordinate on an integral projective curve gives a finite flat map.
Source: finiteness of compact-curve maps and torsion-freeness over projective-line stalks. -/
theorem s0_finite_flat_of_holomorphic_sphere_coordinate
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (q : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    (e : C ≃ₜ ComplexPoint X)
    (h : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e x))))
    (hnc : ∃ x y : C, Point.map q (e x) ≠ Point.map q (e y)) :
    IsFinite q.left ∧ Flat q.left := by
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  letI : IsProjective A.hom := s0_projective_space_projective 1 (Spec ↧ℂ)
  letI : IsIntegral A.left := s0_complex_projective_integral 1
  letI : IsFinite q.left := s0_finite_of_holomorphic_sphere_coordinate X q e h hnc
  let g : C → OnePoint ℂ := fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e x))
  have hgn : ∃ x y, g x ≠ g y := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨x, y, fun he ↦ hxy (s0_sphere_projective_homeomorph.symm.injective he)⟩
  have hgs := b4cov_surjective (Module.finrank_self ℂ) g h hgn
  have hqs : Function.Surjective (Point.map q) := by
    intro y
    obtain ⟨x, hx⟩ := hgs (s0_sphere_projective_homeomorph.symm y)
    exact ⟨e x, s0_sphere_projective_homeomorph.symm.injective hx⟩
  letI : IsDominant q.left := s0_dominant_of_surjective_complex_points X A q hqs
  exact ⟨inferInstance,
    s0_flat_of_dominant_dedekind_stalks q.left s0_projective_line_stalk_dedekind⟩

#print axioms s0_finite_flat_of_holomorphic_sphere_coordinate
end HodgeLean.Foundations.Program
