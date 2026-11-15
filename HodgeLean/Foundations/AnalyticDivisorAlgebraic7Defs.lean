import HodgeLean.Foundations.AnalyticDivisorAlgebraic6Defs

/-! # Definitions for local analytic components

This file records association of analytic function germs at a point.  It is the function-level
form of association in the local analytic ring.  HC no distance; AV milestone no distance.
-/

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic7

/-- Two analytic functions are associated at a point when one is a nonvanishing analytic unit
times the other as germs there.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1. -/
def AreAssociatedAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (y : E) : Prop :=
  ∃ u : E → ℂ, AnalyticAt ℂ u y ∧ u y ≠ 0 ∧ f =ᶠ[nhds y] fun x ↦ u x * g x

example : AreAssociatedAt (fun z : ℂ ↦ 2 * z) (fun z : ℂ ↦ z) 0 := by
  refine ⟨fun _ ↦ 2, analyticAt_const, by norm_num, ?_⟩
  exact Eventually.of_forall fun z ↦ rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic7
