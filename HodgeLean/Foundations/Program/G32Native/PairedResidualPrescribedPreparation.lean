import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemAnalytic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Prescribed full-system preparation degrees -/
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

/-- A specified full-system divisor multiplicity fixes the exact preparation degree. -/
theorem residual_system_prescribed_preparation
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
    (d : ℕ)
    (hd : (d : ℤ) = (b4c_divForm (hE := hE) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) p) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ Set.range y then z else 1) *
        HurwitzPrymRR_loc hE ((∑ i, a i • b i : W).val) p z =
          g (a, z)) ∧
      analyticOrderAt (fun z => g (a, z)) 0 = d ∧
          ∃ u : (Fin m → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
            ∃ c : Fin d → (Fin m → ℂ) → ℂ,
              (∀ j, AnalyticAt ℂ (c j) 0 ∧ c j 0 = 0) ∧
              (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
                fun tz => u tz * HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c tz := by
  obtain ⟨g, hg, he, hp⟩ := residual_system_local_preparation hE y hy W hW b p
  obtain ⟨d', hd', ho, u, hu, hu0, c, hc, hprep⟩ := hp a ha
  have hdd : d' = d := by exact_mod_cast hd'.trans hd.symm
  subst d'
  exact ⟨g, hg, he, ho, u, hu, hu0, c, hc, hprep⟩

#print axioms residual_system_prescribed_preparation
end HodgeLean.Foundations.Program.G32Native
