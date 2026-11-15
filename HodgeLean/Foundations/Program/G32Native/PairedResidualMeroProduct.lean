import HodgeLean.Foundations.Program.RiemannRoch

/-! # Actual meromorphic products and their differential divisors -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Multiply the specified differential by the specified sphere-valued meromorphic function. -/
def residualMeroProduct (hE : Module.finrank ℂ E = 1)
    (f : b4c_MeroFun E C) (w : b4c_MeroForm E C hE) : b4c_MeroForm E C hE :=
  ⟨fun v => (f v.1).elim 0 id * w v, RiemannRochEichler_mul_meroForm hE f w⟩

#print axioms residualMeroProduct
/-- Product coefficient orders retain the exact sum of the two literal divisor coefficients. -/
theorem residualMeroProduct_order [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hf : ∃ p, f p ≠ (0 : ℂ)) (w : b4c_MeroForm E C hE)
    (hw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤) (p : C) :
    meromorphicOrderAt (HurwitzPrymRR_loc hE (residualMeroProduct hE f w) p) 0 =
      ((b4c_div E f p + b4c_divForm (hE := hE) w p : ℤ) : WithTop ℤ) := by
  rw [RiemannRochAna_div_apply_of_finite f (b4c_meroFun_orderSupport_finite hE f) p]
  change meromorphicOrderAt (RiemannRochEichler_functionLocal hE f p *
    HurwitzPrymRR_loc hE w p) 0 = _
  have hfm : MeromorphicAt (RiemannRochEichler_functionLocal hE f p) 0 :=
    RiemannRochEichler_fun_loc_meromorphic hE f p
  rw [meromorphicOrderAt_mul hfm (w.property.2 p),
    ← RiemannRochEichler_ord_eq_local hE f hf p,
    ← RiemannRochEichler_divForm_order hE w hw p, WithTop.coe_add]

#print axioms residualMeroProduct_order
/-- Multiplication adds the actual differential and function divisors without changing multiplicities. -/
theorem residualMeroProduct_divisor [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C)
    (hf : ∃ p, f p ≠ (0 : ℂ)) (w : b4c_MeroForm E C hE)
    (hw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤) :
    b4c_divForm (hE := hE) (residualMeroProduct hE f w) =
      b4c_div E f + b4c_divForm (hE := hE) w := by
  have hn : ∃ p, meromorphicOrderAt
      (HurwitzPrymRR_loc hE (residualMeroProduct hE f w) p) 0 ≠ ⊤ := by
    let p := hw.choose
    exact ⟨p, by rw [residualMeroProduct_order hE f hf w hw p]; exact WithTop.coe_ne_top⟩
  ext p
  apply WithTop.coe_injective
  rw [RiemannRochEichler_divForm_order hE (residualMeroProduct hE f w) hn p,
    Finsupp.add_apply]
  exact residualMeroProduct_order hE f hf w hw p

#print axioms residualMeroProduct_divisor
end HodgeLean.Foundations.Program.G32Native
