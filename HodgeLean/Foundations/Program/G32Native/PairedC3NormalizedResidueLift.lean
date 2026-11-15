import HodgeLean.Foundations.Program.G32Native.PairedC3FullResidueLift
import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleNormalization

/-! # Evaluation surjectivity in the specified normalized full pole space -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters HodgeLean.Foundations.Program TauCeti.Contour
open scoped Manifold ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Every total-zero residue vector is attained in the specified full
normalized pole space, with the actual residue evaluations retained.
Source: Forster, Lectures on Riemann Surfaces, §18; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.3(i). -/
theorem paired_c3_normalized_full_residue_lift (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin (n + 1) → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0)
    (a : Fin (n + 1) → ℂ) (ha : ∑ i, a i = 0) :
    ∃ q : W, ∀ i, b4c_res (hE := h) q.val (y i) = a i := by
  classical
  obtain ⟨w, hr, ho, hout⟩ := paired_c3_full_residue_lift h n y hy a ha
  let S := Finset.univ.image y
  have hS (p : C) : p ∈ S ↔ p ∈ Set.range y := by simp [S]
  let q := residual_normalize_poles S (w : TangentBundle 𝓘(ℂ, E) C → ℂ)
  have hg (p : C) : HurwitzPrymRR_loc h q p =ᶠ[𝓝[≠] 0] HurwitzPrymRR_loc h w p :=
    residual_normalize_poles_loc h S w p
  have hq : q ∈ W := by
    apply (hW q).mpr
    refine ⟨⟨?_, fun p => (w.property.2 p).congr (hg p).symm⟩, ?_, ?_, ?_⟩
    · intro p c u v
      change (if p ∈ S then 0 else _) =
        c * (if p ∈ S then 0 else _) + (if p ∈ S then 0 else _)
      by_cases hp : p ∈ S
      · simp only [if_pos hp, mul_zero, add_zero]
      · simp only [if_neg hp]
        exact w.property.1 p c u v
    · intro p
      rw [meromorphicOrderAt_congr (hg p)]
      exact ho p
    · intro p hp
      have hz : HurwitzPrymRR_loc h q p 0 = HurwitzPrymRR_loc h w p 0 := by
        rw [RiemannRochEichler_loc_zero, RiemannRochEichler_loc_zero]
        change (if p ∈ S then 0 else _) = _
        exact if_neg (fun hpS => hp ((hS p).mp hpS))
      exact (hout p hp).congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hg p) hz).symm
    · intro p hp u
      change (if p ∈ S then 0 else _) = 0
      exact if_pos ((hS p).mpr hp)
  refine ⟨⟨q, hq⟩, ?_⟩
  intro i
  exact (residue_congr_nhdsNE (hg (y i))).trans (hr i)

#print axioms paired_c3_normalized_full_residue_lift
end HodgeLean.Foundations.Program.G32Native
