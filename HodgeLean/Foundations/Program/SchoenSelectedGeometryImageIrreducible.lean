import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticPreimage
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveImage

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The Zariski image of a connected complex manifold under a holomorphic map is irreducible.
Source: the analytic identity principle applied to preimages of algebraic subsets. -/
theorem s0_holomorphic_image_irreducible
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : C → ComplexPoint X)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω f) :
    IsIrreducible (range (fun x ↦ (f x).underlying)) := by
  refine ⟨Set.range_nonempty _, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hcover
  let P := f ⁻¹' ((Point.underlying : ComplexPoint X → X.left) ⁻¹' A)
  let Q := f ⁻¹' ((Point.underlying : ComplexPoint X → X.left) ⁻¹' B)
  have hP : IsClosedAnalytic ℂ P := s0_closedAnalytic_preimage f hf _
    (spec_isClosedAnalytic_preimage_underlying X hA)
  have hQ : IsClosedAnalytic ℂ Q := s0_closedAnalytic_preimage f hf _
    (spec_isClosedAnalytic_preimage_underlying X hB)
  by_cases hi : (interior P).Nonempty
  · have hPu : P = univ := hP.eq_univ_of_nonempty_interior hi
    refine Or.inl ?_
    rintro _ ⟨x, rfl⟩
    exact (show x ∈ P from hPu ▸ mem_univ x)
  · have hPi : interior P = ∅ := not_nonempty_iff_eq_empty.mp hi
    have hd : closure Pᶜ = univ := by rw [closure_compl, hPi, compl_empty]
    have hsub : Pᶜ ⊆ Q := by
      intro x hx
      exact (hcover (mem_range_self x)).resolve_left hx
    have hQu : univ ⊆ Q := by
      rw [← hd]
      exact closure_minimal hsub hQ.1
    refine Or.inr ?_
    rintro _ ⟨x, rfl⟩
    exact hQu (mem_univ x)

#print axioms s0_holomorphic_image_irreducible
end HodgeLean.Foundations.Program
