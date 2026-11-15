import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial
import HodgeLean.Foundations.Program.SchoenCyclePrescribedPreparation
import HodgeLean.Foundations.Program.SchoenCyclePairedPreparedDivisibility

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

/-- At an absent divisor point every parameter variation is locally divisible.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local equations of divisors. -/
theorem s2e_paired_variation_divisible_off_divisor
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
    (δ : Fin m → ℂ)
    (hzero : s2e_adjustedDifferentialDivisor hE w y (∑ i, a i • b i) p = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        HurwitzPrymRR_loc hE
          (s2e_pairedDifferentialLinear hE w (∑ i, δ i • b i)) p z =
        q z * HurwitzPrymRR_loc hE
          (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) p z := by
  obtain ⟨g, hg, he, _, u, hu, hu0, c, hc, hprep⟩ :=
    s2e_paired_family_prescribed_preparation hE w x hres y hy horder hout b p a ha 0
      (by simpa only [Nat.cast_zero] using hzero.symm)
  exact s2e_paired_prepared_local_divisibility hE w y b a δ p g u c
    (hg a) he hu hu0 (fun j => (hc j).1) (fun j => Fin.elim0 j) hprep

end HodgeLean.Foundations.Program
