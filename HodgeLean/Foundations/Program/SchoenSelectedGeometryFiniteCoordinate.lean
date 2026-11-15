import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexFibers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A nonconstant holomorphic sphere coordinate on a compact curve makes its algebraic
projective-line projection finite.
Source: Forster, Lectures on Riemann Surfaces, §4.23, and the proper quasi-finite criterion. -/
theorem s0_finite_of_holomorphic_sphere_coordinate
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (q : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    (e : C ≃ₜ ComplexPoint X)
    (h : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e x))))
    (hnc : ∃ x y : C, Point.map q (e x) ≠ Point.map q (e y)) : IsFinite q.left := by
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  letI : IsProjective A.hom := s0_projective_space_projective 1 (Spec ↧ℂ)
  haveI : IsProper (q.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsProper q.left := IsProper.of_comp q.left A.hom
  apply s0_finite_of_finite_complex_fibers X A q
  intro y
  let g : C → OnePoint ℂ := fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e x))
  have hgn : ∃ x y, g x ≠ g y := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨x, y, fun he ↦ hxy (s0_sphere_projective_homeomorph.symm.injective he)⟩
  have hfin := b4cov_fiber_finite (Module.finrank_self ℂ)
    g h hgn (s0_sphere_projective_homeomorph.symm y)
  apply (hfin.image e).subset
  intro z hz
  refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
  change s0_sphere_projective_homeomorph.symm (Point.map q (e (e.symm z))) = _
  rw [e.apply_symm_apply, show Point.map q z = y from hz]

#print axioms s0_finite_of_holomorphic_sphere_coordinate
end HodgeLean.Foundations.Program
