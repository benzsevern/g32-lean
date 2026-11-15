import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticRetraction

noncomputable section
set_option maxHeartbeats 400000
open Set
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Local holomorphic left inverses give analytic equations for a closed image.
Source: the local retraction criterion for complex submanifolds. -/
theorem s0_image_analytic_of_local_left_inverses
    (n : ℕ) {C M : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [TopologicalSpace M]
    [ChartedSpace (Fin n → ℂ) M] [IsManifold 𝓘(ℂ, Fin n → ℂ) ω M]
    (f : C → M) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin n → ℂ) ω f)
    (hc : IsClosed (range f))
    (hl : ∀ x : C, ∃ V : Set M, IsOpen V ∧ f x ∈ V ∧ ∃ g : M → C,
      (∀ y ∈ V, ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω g y) ∧
      ∀ z : C, f z ∈ V → g (f z) = z) :
    IsClosedAnalytic (Fin n → ℂ) (range f) := by
  apply s0_closedAnalytic_of_local_retractions n (range f) hc
  rintro _ ⟨x, rfl⟩
  obtain ⟨V, ho, hx, g, hg, hgf⟩ := hl x
  refine ⟨V, ho, hx, f ∘ g, fun y hy ↦ (hf (g y)).comp y (hg y hy), ?_⟩
  intro y hy
  constructor
  · rintro ⟨z, rfl⟩
    change f (g (f z)) = f z
    rw [hgf z hy]
  · intro he
    exact ⟨g y, he⟩

#print axioms s0_image_analytic_of_local_left_inverses
end HodgeLean.Foundations.Program
