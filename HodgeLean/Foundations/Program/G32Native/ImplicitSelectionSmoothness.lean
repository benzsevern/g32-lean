import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Smoothness of a common selection from a unique implicit branch

A continuous selection of solutions agrees near the reference point with the
analytic branch supplied by the implicit function theorem.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

/-- A selection tending to the reference solution inherits analyticity from the
implicit equation. No independently chosen local selection remains in the output.
Source: Mathlib, `ContDiffAt.eventually_apply_eq_iff_implicitFunction` and
`ContDiffAt.contDiffAt_implicitFunction`.
HC no distance; AV milestone no distance. -/
theorem implicit_selection_contDiffAt
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (G : E × B → B) (y : E) (b : B) (p : E → B)
    (hG : ContDiffAt ℝ ⊤ G (y, b))
    (hInv : (fderiv ℝ G (y, b) ∘L ContinuousLinearMap.inr ℝ E B).IsInvertible)
    (hp : Tendsto p (𝓝 y) (𝓝 b))
    (hsol : ∀ᶠ z in 𝓝 y, G (z, p z) = G (y, b)) :
    ContDiffAt ℝ ⊤ p y := by
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hG.implicitFunction hn hInv
  have hψ : ContDiffAt ℝ ⊤ ψ y := hG.contDiffAt_implicitFunction hn hInv
  have ht : Tendsto (fun z => (z, p z)) (𝓝 y) (𝓝 (y, b)) :=
    tendsto_id.prodMk_nhds hp
  have heq := ht.eventually (hG.eventually_apply_eq_iff_implicitFunction hn hInv)
  have hmatch : p =ᶠ[𝓝 y] ψ := by
    filter_upwards [heq, hsol] with z hz hs
    exact ((hz.mp hs) : ψ z = p z).symm
  exact hψ.congr_of_eventuallyEq hmatch

#print axioms implicit_selection_contDiffAt

end HodgeLean.Foundations.TubularEuler
