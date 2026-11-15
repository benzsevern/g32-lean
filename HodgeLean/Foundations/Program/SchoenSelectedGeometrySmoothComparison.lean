import HodgeLean.Foundations.Program.SchoenSelectedGeometryHolomorphicLift

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A smooth curve model with a holomorphic ambient comparison is biholomorphic to the surface.
Source: local left inverses of smooth algebraic closed immersions and the inverse theorem for curves. -/
theorem s0_biholomorphic_of_smooth_curve_ambient_comparison
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (hd : TopologicalSpace.dim Y.left = 1)
    (i : Y ⟶ X) [IsClosedImmersion i.left] (e : C ≃ₜ ComplexPoint Y)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω
      (fun x ↦ Point.map i (e x))) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y.left) → ℂ) ω e ∧
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm := by
  have he := s0_holomorphic_lift_of_closed_immersion X Y
    (TopologicalSpace.dim X.left) (TopologicalSpace.dim Y.left) i e e.continuous hf
  refine ⟨he, s0_curve_homeomorph_inverse_holomorphic ?_ e he⟩
  simp [hd]

#print axioms s0_biholomorphic_of_smooth_curve_ambient_comparison
end HodgeLean.Foundations.Program
