import HodgeLean.Foundations.Program.G32Native.PairedC3RegularRelations
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Quotient.Pi

/-! # Independence of the conormal classes of regular equations -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
open RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- A linear combination of regular equations lies in the square of their
ideal exactly when all its coefficients lie in that ideal.
Source: Hartshorne, Algebraic Geometry, II.8, the conormal basis of a
regular immersion. -/
theorem paired_c3_regular_square_coefficients
    {A : Type*} [CommRing A] {n : ℕ} (f c : Fin n → A)
    (hreg : IsWeaklyRegular A (List.ofFn f)) :
    (∑ i, c i * f i) ∈ (Ideal.span (Set.range f)) ^ 2 ↔
      ∀ i, c i ∈ Ideal.span (Set.range f) := by
  classical
  let I := Ideal.span (Set.range f)
  constructor
  · intro h
    have hm : (∑ i, c i * f i) ∈ I • Submodule.span A (Set.range f)  := by
      change (∑ i, c i * f i) ∈ I * I
      simpa only [pow_two] using h
    obtain ⟨b, hb, he⟩ :=
      (Submodule.mem_ideal_smul_span_iff_exists_sum I f _).mp hm
    have he' : ∑ i, b i * f i = ∑ i, c i * f i := by
      simpa [Finsupp.sum_fintype] using he
    have hz : ∑ i, (c i - b i) * f i = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [he', sub_self]
    have hc := paired_c3_regular_relation_coefficients f (fun i => c i - b i) hreg hz
    intro i
    simpa only [sub_add_cancel] using I.add_mem (hc i) (hb i)
  · intro h
    rw [pow_two]
    exact (I * I).sum_mem fun i _ => Ideal.mul_mem_mul (h i)
      (Ideal.subset_span (Set.mem_range_self i))

#print axioms paired_c3_regular_square_coefficients
end HodgeLean.Foundations.Program.G32Native
