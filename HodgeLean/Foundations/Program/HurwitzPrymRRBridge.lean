import HodgeLean.Foundations.Program.HurwitzPrymCovDegree

noncomputable section

open Manifold
open scoped ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

theorem b4_fiber_finite_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y : Y) :
    (f ⁻¹' {y}).Finite := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  exact b4cov_fiber_finite hE f hf hnc y

theorem b4_fiberDegree_eq_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [ConnectedSpace Y]
    (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y y' : Y) :
    b4_fiberDegree E E' f y = b4_fiberDegree E E' f y' := by
  exact b4cov_fiberDegree_eq hE hE' f hf hnc y y'

end HodgeLean.Foundations.Program
