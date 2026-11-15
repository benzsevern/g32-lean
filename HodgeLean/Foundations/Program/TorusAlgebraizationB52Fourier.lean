import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section
open MeasureTheory
namespace HodgeLean.Foundations.Program

theorem b52_probability_invariant_measure (G : Type*) [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    ∃ μ : Measure G, μ.IsAddLeftInvariant ∧ IsProbabilityMeasure μ := by
  let K : TopologicalSpace.PositiveCompacts G := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  refine ⟨Measure.addHaarMeasure K, inferInstance, ?_⟩
  constructor
  exact Measure.addHaarMeasure_self

#print axioms b52_probability_invariant_measure

theorem b52_integral_nontrivial_character {G : Type*}
    [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant] (f : G → ℂ)
    (hf : ∀ x y, f (x + y) = f x * f y) (hne : ∃ x, f x ≠ 1) :
    ∫ x, f x ∂μ = 0 := by
  obtain ⟨g, hg⟩ := hne
  have h := integral_add_left_eq_self (μ := μ) f g
  simp_rw [hf g, integral_const_mul] at h
  have hz : (f g - 1) * (∫ x, f x ∂μ) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hg)

#print axioms b52_integral_nontrivial_character

theorem b52_character_series_integral {G ι : Type*}
    [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] [Zero ι] [Countable ι]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (f : ι → G → ℂ) (hf : ∀ i x y, f i (x + y) = f i x * f i y)
    (hzero : ∀ x, f 0 x = 1) (hne : ∀ i, i ≠ 0 → ∃ x, f i x ≠ 1)
    (hint : ∀ i, Integrable (f i) μ) (hnorm : ∀ i x, ‖f i x‖ = 1)
    (c : ι → ℂ) (hc : Summable (fun i ↦ ‖c i‖)) :
    (∫ x, (∑' i, c i * f i x) ∂μ) = c 0 := by
  have hsum : Summable (fun i ↦ ∫ x, ‖c i * f i x‖ ∂μ) := by
    simpa [norm_mul, hnorm] using hc
  rw [← integral_tsum_of_summable_integral_norm (fun i ↦ (hint i).const_mul (c i)) hsum]
  simp_rw [integral_const_mul]
  rw [tsum_eq_single 0 (fun i hi ↦ ?_)]
  · simp [hzero]
  · rw [b52_integral_nontrivial_character μ (f i) (hf i) (hne i hi), mul_zero]

#print axioms b52_character_series_integral

theorem b52_character_series_nonzero {G ι : Type*}
    [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] [Zero ι] [Countable ι]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (f : ι → G → ℂ) (hf : ∀ i x y, f i (x + y) = f i x * f i y)
    (hzero : ∀ x, f 0 x = 1) (hne : ∀ i, i ≠ 0 → ∃ x, f i x ≠ 1)
    (hint : ∀ i, Integrable (f i) μ) (hnorm : ∀ i x, ‖f i x‖ = 1)
    (c : ι → ℂ) (hc : Summable (fun i ↦ ‖c i‖)) (hc0 : c 0 ≠ 0) :
    ∃ x, (∑' i, c i * f i x) ≠ 0 := by
  by_contra! h
  have hi := b52_character_series_integral μ f hf hzero hne hint hnorm c hc
  simp only [h, integral_zero] at hi
  exact hc0 hi.symm

#print axioms b52_character_series_nonzero

end HodgeLean.Foundations.Program
