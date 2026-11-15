import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleEnvelope

/-! # Realizing meromorphic germs in the specified full normalized pole space -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The supplied full pole space realizes every nonzero meromorphic germ system with its pole bound. -/
theorem residual_full_pole_space_realizes_germs [T2Space C] [CompactSpace C]
    (hE : Module.finrank ℂ E = 1) (S : Finset C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm hE q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q p) 0) ∧
      (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q p) 0) ∧
      ∀ p ∈ S, ∀ t, q ⟨p, t⟩ = 0)
    (w : b4c_MeroForm E C hE)
    (hbound : ∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0)
    (hregular : ∀ p ∉ S, 0 ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0)
    (hfinite : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤) :
    ∃ q : W, q ≠ 0 ∧ ∀ p, HurwitzPrymRR_loc hE q.val p =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc hE w p := by
  classical
  obtain ⟨v, hv, hva, _⟩ := RiemannRochEichler_regularize_off_poles hE w (S : Set C) hregular
  let q := residual_normalize_poles (E := E) S v
  have hn (p : C) : HurwitzPrymRR_loc hE q p =ᶠ[𝓝[≠] 0] HurwitzPrymRR_loc hE v p :=
    residual_normalize_poles_loc hE S v p
  have hg (p : C) : HurwitzPrymRR_loc hE q p =ᶠ[𝓝[≠] 0] HurwitzPrymRR_loc hE w p :=
    (hn p).trans (hv p)
  have hq : q ∈ W := by
    apply (hW q).mpr
    refine ⟨⟨?_, fun p => (v.property.2 p).congr (hn p).symm⟩, ?_, ?_, ?_⟩
    · intro p a u t
      change (if p ∈ S then 0 else _) =
        a * (if p ∈ S then 0 else _) + (if p ∈ S then 0 else _)
      by_cases hp : p ∈ S
      · simp only [ite_eq_left hp, mul_zero, add_zero]
      · simp only [ite_eq_right hp]
        exact v.property.1 p a u t
    · intro p
      rw [meromorphicOrderAt_congr (hg p)]
      exact hbound p
    · intro p hp
      have hz : HurwitzPrymRR_loc hE q p 0 = HurwitzPrymRR_loc hE v p 0 := by
        rw [RiemannRochEichler_loc_zero, RiemannRochEichler_loc_zero]
        change (if p ∈ S then 0 else _) = _
        exact ite_eq_right hp
      exact (hva p hp).congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hn p) hz).symm
    · intro p hp t
      change (if p ∈ S then 0 else _) = 0
      exact ite_eq_left hp
  refine ⟨⟨q, hq⟩, ?_, hg⟩
  intro hz
  have hzero : q = 0 := congrArg Subtype.val hz
  obtain ⟨p, hp⟩ := hfinite
  apply hp
  have ho : meromorphicOrderAt (HurwitzPrymRR_loc hE q p) 0 = ⊤ := by
    rw [hzero]
    change meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) 0 = ⊤
    exact meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall (fun _ => rfl))
  exact (meromorphicOrderAt_congr (hg p)).symm.trans ho

#print axioms residual_full_pole_space_realizes_germs
end HodgeLean.Foundations.Program.G32Native
