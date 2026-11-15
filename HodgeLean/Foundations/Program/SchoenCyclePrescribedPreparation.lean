import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Local polynomial preparation of the paired family -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A specified adjusted multiplicity determines the degree of the prepared polynomial.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_paired_family_prescribed_preparation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ)) (p : C)
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (d : ℕ)
    (hd : (d : ℤ) = s2e_adjustedDifferentialDivisor hE w y (∑ i, a i • b i) p) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ Set.range y then z else 1) *
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) p z =
          g (a, z)) ∧
      analyticOrderAt (fun z => g (a, z)) 0 = d ∧
          ∃ u : (Fin m → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
            ∃ c : Fin d → (Fin m → ℂ) → ℂ,
              (∀ j, AnalyticAt ℂ (c j) 0 ∧ c j 0 = 0) ∧
              (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
                fun tz => u tz * HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c tz := by
  obtain ⟨g, hg, he, hp⟩ := s2e_paired_family_local_preparation hE w x hres y hy
    horder hout b p
  obtain ⟨d', hd', ho, u, hu, hu0, c, hc, hprep⟩ := hp a ha
  have hdd : d' = d := by exact_mod_cast hd'.trans hd.symm
  subst d'
  exact ⟨g, hg, he, ho, u, hu, hu0, c, hc, hprep⟩

end HodgeLean.Foundations.Program
