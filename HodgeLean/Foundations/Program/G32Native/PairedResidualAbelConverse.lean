import HodgeLean.Foundations.Program.G32Native.PairedResidualGermRealization
import HodgeLean.Foundations.Program.G32Native.PairedResidualMeroProduct
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelPeriods

/-! # Effective divisors of the full normalized system from their Abel values -/
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

/-- Every effective divisor with the reference degree and Abel value occurs in the specified full space. -/
theorem residual_full_space_divisor_of_abel_value
    (hE : Module.finrank ℂ E = 1) (S : Finset C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm hE q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q p) 0) ∧
      (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q p) 0) ∧
      ∀ p ∈ S, ∀ t, q ⟨p, t⟩ = 0)
    (v : W) (hv : v ≠ 0) (p : C) (M D : C →₀ ℤ)
    (hM : ∀ q, M q ≤ 1) (hMout : ∀ q ∉ S, M q = 0)
    (hD : ∀ q, 0 ≤ D q)
    (hdeg : b4c_deg D = b4c_deg (b4c_divForm (hE := hE) v.val + M))
    (hperiod : weightedSum (analyticAbel (C := C) hE p) D =
      weightedSum (analyticAbel (C := C) hE p) (b4c_divForm (hE := hE) v.val + M)) :
    ∃ q : W, q ≠ 0 ∧ b4c_divForm (hE := hE) q.val + M = D := by
  classical
  have hvW := (hW v.val).mp v.property
  let V : b4c_MeroForm E C hE := ⟨v.val, hvW.1⟩
  have hv0 : (V : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hv (Subtype.ext h)
  have hgv := residual_normalized_form_has_finite_order hE (S : Set C) V hv0
    hvW.2.2.1 hvW.2.2.2
  have hd0 : b4c_deg (D - (b4c_divForm (hE := hE) v.val + M)) = 0 := by
    rw [RiemannRochAna_deg_sub, hdeg, sub_self]
  have hp0 : weightedSum (analyticAbel (C := C) hE p)
      (D - (b4c_divForm (hE := hE) v.val + M)) = 0 := by
    rw [map_sub, hperiod, sub_self]
  obtain ⟨f, hf, hfd⟩ := meromorphicFunction_of_abelSum_zero (C := C) hE p _ hd0 hp0
  have ho (q : C) :
      meromorphicOrderAt (HurwitzPrymRR_loc hE (residualMeroProduct hE f V) q) 0 =
        ((D q - M q : ℤ) : WithTop ℤ) := by
    rw [residualMeroProduct_order hE f hf V hgv q, hfd]
    simp only [Finsupp.sub_apply, Finsupp.add_apply, V]
    congr 1
    omega
  have hb : ∀ q, ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (HurwitzPrymRR_loc hE (residualMeroProduct hE f V) q) 0 := by
    intro q
    rw [ho q, WithTop.coe_le_coe]
    have := hM q
    have := hD q
    omega
  have hr : ∀ q ∉ S, 0 ≤
      meromorphicOrderAt (HurwitzPrymRR_loc hE (residualMeroProduct hE f V) q) 0 := by
    intro q hq
    rw [ho q, hMout q hq, sub_zero]
    exact WithTop.coe_le_coe.mpr (hD q)
  have hn : ∃ q, meromorphicOrderAt
      (HurwitzPrymRR_loc hE (residualMeroProduct hE f V) q) 0 ≠ ⊤ := by
    obtain ⟨q, _⟩ := hgv
    exact ⟨q, by rw [ho q]; exact WithTop.coe_ne_top⟩
  obtain ⟨q, hq, hg⟩ := residual_full_pole_space_realizes_germs hE S W hW
    (residualMeroProduct hE f V) hb hr hn
  refine ⟨q, hq, ?_⟩
  have hqdiv := residual_divisor_eq_of_germs hE q.val (residualMeroProduct hE f V).val hg
  rw [hqdiv, residualMeroProduct_divisor hE f hf V hgv, hfd]
  change (D - (b4c_divForm (hE := hE) v.val + M) + b4c_divForm (hE := hE) v.val) + M = D
  abel

#print axioms residual_full_space_divisor_of_abel_value
end HodgeLean.Foundations.Program.G32Native
