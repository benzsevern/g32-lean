import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial
import HodgeLean.Foundations.Program.G32Native.PairedResidualPrescribedPreparation
import HodgeLean.Foundations.Program.G32Native.PairedResidualPreparedDivisibility

/-! # Local polynomial preparation of the paired family -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Outside the full-system adjusted divisor every variation is locally divisible. -/
theorem residual_system_variation_divisible_off_divisor
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n m : ℕ}
    (y : Fin n → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (b : Fin m → W) (p : C)
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (δ : Fin m → ℂ)
    (hzero : (b4c_divForm (hE := hE) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) p = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        HurwitzPrymRR_loc hE
          ((∑ i, δ i • b i : W).val) p z =
        q z * HurwitzPrymRR_loc hE
          ((∑ i, a i • b i : W).val) p z := by
  obtain ⟨g, hg, he, _, u, hu, hu0, c, hc, hprep⟩ :=
    residual_system_prescribed_preparation hE y hy W hW b p a ha 0
      (by simpa only [Nat.cast_zero] using hzero.symm)
  exact residual_system_prepared_local_divisibility hE y W b a δ p g u c
    (hg a) he hu hu0 (fun j => (hc j).1) (fun j => Fin.elim0 j) hprep

#print axioms residual_system_variation_divisible_off_divisor
end HodgeLean.Foundations.Program.G32Native
