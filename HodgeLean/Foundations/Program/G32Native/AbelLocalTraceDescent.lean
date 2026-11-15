import HodgeLean.Foundations.Program.G32Native.LocalLiftConstancy
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Monoid

/-! # Literal primitive traces from local Abel lifts -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Equal quotient traces of continuous lifts give a literal local vector trace plus one constant. -/
theorem local_abel_lift_trace
    {V T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace T] [AddCommGroup T]
    (q : V →+ T) (hq : IsLocalHomeomorph q) {ι : Type*} [Fintype ι]
    (f : (ι → ℂ) → V) (h : ι → ℂ → V)
    (hf : ContinuousAt f 0) (hh : ∀ i, ContinuousAt (h i) 0)
    (he : ∀ᶠ z in 𝓝 (0 : ι → ℂ), q (f z) = ∑ i, q (h i (z i))) :
    ∃ c : V, ∀ᶠ z in 𝓝 (0 : ι → ℂ), f z = (∑ i, h i (z i)) + c := by
  let s : (ι → ℂ) → V := fun z => ∑ i, h i (z i)
  have hs : ContinuousAt s 0 := by
    apply tendsto_finsetSum
    intro i _
    have hi : ContinuousAt (fun z : ι → ℂ => z i) (0 : ι → ℂ) :=
      (continuous_apply i).continuousAt
    exact ((hh i).comp_of_eq hi rfl).tendsto
  let d := fun z => f z - s z
  have hd : ContinuousAt d 0 := hf.sub hs
  have heq : ∀ᶠ z in 𝓝 (0 : ι → ℂ), q (d z) = 0 := by
    filter_upwards [he] with z hz
    change q (f z - ∑ i, h i (z i)) = 0
    rw [map_sub, map_sum, hz, sub_self]
  have hc := local_homeomorph_lift_eventually_constant q hq hd
    (heq.mono fun _ hz => hz.trans heq.self_of_nhds.symm)
  refine ⟨d 0, hc.mono fun z hz => ?_⟩
  exact (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)

/-- Every linear period functional gives the literal scalar primitive trace with the same fixed normalization. -/
theorem local_abel_lift_scalar_trace
    {V T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace T] [AddCommGroup T]
    (q : V →+ T) (hq : IsLocalHomeomorph q) {ι : Type*} [Fintype ι]
    (f : (ι → ℂ) → V) (h : ι → ℂ → V)
    (hf : ContinuousAt f 0) (hh : ∀ i, ContinuousAt (h i) 0)
    (he : ∀ᶠ z in 𝓝 (0 : ι → ℂ), q (f z) = ∑ i, q (h i (z i)))
    (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ c : ℂ, ∀ᶠ z in 𝓝 (0 : ι → ℂ), ℓ (f z) = (∑ i, ℓ (h i (z i))) + c := by
  obtain ⟨c, hc⟩ := local_abel_lift_trace q hq f h hf hh he
  refine ⟨ℓ c, hc.mono fun z hz => ?_⟩
  rw [hz, map_add, map_sum]

#print axioms local_abel_lift_trace
#print axioms local_abel_lift_scalar_trace
end HodgeLean.Foundations.Program.G32Native
