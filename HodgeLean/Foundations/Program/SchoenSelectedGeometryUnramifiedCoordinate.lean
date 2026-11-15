import HodgeLean.Foundations.Program.SchoenSelectedGeometryFlatCoordinate
import HodgeLean.Foundations.Program.SchoenSelectedGeometryUnramifiedInverse

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An unramified sphere coordinate gives a finite flat algebraic map injective on an analytic neighborhood.
Source: the holomorphic inverse function theorem and finite flatness of curve coordinates. -/
theorem s0_finite_flat_locally_injective_coordinate
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (q : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    (e : C ≃ₜ ComplexPoint X)
    (h : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e x))))
    (x : C)
    (hd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun z ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e z))) x ≠ 0) :
    IsFinite q.left ∧ Flat q.left ∧ ∃ N : Set (ComplexPoint X),
      IsOpen N ∧ e x ∈ N ∧ Set.InjOn (Point.map q) N := by
  classical
  let g : C → OnePoint ℂ := fun z ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e z))
  have hn : ∃ a b : C, Point.map q (e a) ≠ Point.map q (e b) := by
    by_contra! hc
    have he : g = fun _ ↦ g x := funext (fun z ↦ congrArg s0_sphere_projective_homeomorph.symm (hc z x))
    apply hd
    change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x = 0
    rw [he]
    exact mfderiv_const
  obtain ⟨hfin, hflat⟩ := s0_finite_flat_of_holomorphic_sphere_coordinate X q e h hn
  obtain ⟨r, _, _, hr⟩ := s0_unramified_curve_local_inverse g h x hd
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hr
  refine ⟨hfin, hflat, e.symm ⁻¹' U, hUopen.preimage e.symm.continuous, ?_, ?_⟩
  · simpa using hxU
  · intro a ha b hb hab
    apply e.symm.injective
    have hga : r (g (e.symm a)) = e.symm a := hUsub ha
    have hgb : r (g (e.symm b)) = e.symm b := hUsub hb
    rw [← hga, ← hgb]
    apply congrArg r
    dsimp [g]
    rw [e.apply_symm_apply, e.apply_symm_apply, hab]

#print axioms s0_finite_flat_locally_injective_coordinate
end HodgeLean.Foundations.Program
