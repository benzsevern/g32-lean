import HodgeLean.Foundations.Analytic.Analytification

/-! # Literal constant translations of holomorphic coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Subtracting a literal complex constant preserves the original holomorphic function predicate.
Source: an_Atlas.IsHolFun; AnalyticAt.sub.
HC no distance; AV milestone no distance. -/
lemma properCycle_holomorphic_sub_const
    {X : Type} [TopologicalSpace X] (S : an_ReducedSpace X) (U : Set X)
    (f : U → ℂ) (hf : S.IsHolFun f) (c : ℂ) :
    S.IsHolFun (fun x => f x - c) := by
  intro x j hx
  obtain ⟨V, hV, hxV, G, hG, hEq⟩ := hf x j hx
  refine ⟨V, hV, hxV, fun z => G z - c, hG.sub analyticAt_const, ?_⟩
  intro y hy
  exact congrArg (fun z : ℂ => z - c) (hEq y hy)

end HodgeLean.Foundations.QuotientDuality
