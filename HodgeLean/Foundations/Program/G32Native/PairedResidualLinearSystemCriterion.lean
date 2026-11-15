import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelConverse

/-! # Abel criterion for the fixed full normalized pole system -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Among effective divisors of the reference degree, the fixed full system is exactly its Abel class. -/
theorem residual_full_space_divisor_abel_criterion
    (hE : Module.finrank ℂ E = 1) (S : Finset C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm hE q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q p) 0) ∧
      (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q p) 0) ∧
      ∀ p ∈ S, ∀ t, q ⟨p, t⟩ = 0)
    {n : ℕ} (y : Fin n → C) (hy : Function.Injective y)
    (hS : ∀ q, q ∈ S ↔ q ∈ Set.range y)
    (v : W) (hv : v ≠ 0) (p : C) (D : C →₀ ℤ) (hD : ∀ q, 0 ≤ D q)
    (hdeg : b4c_deg D = b4c_deg (b4c_divForm (hE := hE) v.val + s2e_markedPoleDivisor y)) :
    (∃ q : W, q ≠ 0 ∧ b4c_divForm (hE := hE) q.val + s2e_markedPoleDivisor y = D) ↔
      weightedSum (analyticAbel (C := C) hE p) D =
        weightedSum (analyticAbel (C := C) hE p)
          (b4c_divForm (hE := hE) v.val + s2e_markedPoleDivisor y) := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have he := residual_normalized_divisor_abel_sum_eq hE (S : Set C) W
      (fun q => ⟨((hW q.val).mp q.property).1, ((hW q.val).mp q.property).2.2⟩)
      q v hq hv p (s2e_markedPoleDivisor y)
    exact (congrArg (weightedSum (analyticAbel (C := C) hE p)) heq).symm.trans he
  · intro hp
    apply residual_full_space_divisor_of_abel_value hE S W hW v hv p
      (s2e_markedPoleDivisor y) D ?_ ?_ hD hdeg hp
    · intro q
      by_cases hq : q ∈ Set.range y
      · obtain ⟨j, rfl⟩ := hq
        rw [s2e_markedPoleDivisor_apply_of_injective y hy j]
      · rw [s2e_markedPoleDivisor_apply_outside y q hq]
        norm_num
    · intro q hq
      exact s2e_markedPoleDivisor_apply_outside y q (fun hr => hq ((hS q).mpr hr))

#print axioms residual_full_space_divisor_abel_criterion
end HodgeLean.Foundations.Program.G32Native
