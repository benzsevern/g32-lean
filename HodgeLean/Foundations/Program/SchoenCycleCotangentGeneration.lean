import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Ideal.Operations

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Generators of the cotangent ideal generate a finitely generated local maximal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 2,
Proposition 2.8; Mathlib, Submodule.le_of_le_smul_of_le_jacobson_bot. -/
theorem s2e_maximalIdeal_eq_span_of_cotangent_generators
    {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*} (c : ι → R)
    (hfg : (IsLocalRing.maximalIdeal R).FG)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
    (hgen : IsLocalRing.maximalIdeal R ≤
      Ideal.span (Set.range c) ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R = Ideal.span (Set.range c) := by
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    simpa only [Ideal.smul_eq_mul, pow_two] using hgen
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hc i

#print axioms s2e_maximalIdeal_eq_span_of_cotangent_generators

/-- Perturbing local maximal-ideal generators by elements of its square preserves generation.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 2,
Proposition 2.8, applied to the maximal ideal. -/
theorem s2e_maximalIdeal_generators_stable_mod_square
    {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*} (c d : ι → R)
    (hfg : (IsLocalRing.maximalIdeal R).FG)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span (Set.range c))
    (hdiff : ∀ i, d i - c i ∈ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R = Ideal.span (Set.range d) := by
  have hc (i : ι) : c i ∈ IsLocalRing.maximalIdeal R := by
    rw [hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hm2 : IsLocalRing.maximalIdeal R ^ 2 ≤ IsLocalRing.maximalIdeal R :=
    Ideal.pow_le_self (by decide)
  apply s2e_maximalIdeal_eq_span_of_cotangent_generators d hfg
  · intro i
    have h := (IsLocalRing.maximalIdeal R).add_mem (hm2 (hdiff i)) (hc i)
    simpa only [sub_add_cancel] using h
  · let J : Ideal R := Ideal.span (Set.range d) ⊔ IsLocalRing.maximalIdeal R ^ 2
    have hs : Ideal.span (Set.range c) ≤ J := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hleft : Ideal.span (Set.range d) ≤ J := le_sup_left
      have hright : IsLocalRing.maximalIdeal R ^ 2 ≤ J := le_sup_right
      have hd : d i ∈ J := hleft (Ideal.subset_span ⟨i, rfl⟩)
      have he : d i - c i ∈ J := hright (hdiff i)
      change c i ∈ J
      simpa only [sub_sub_cancel] using J.sub_mem hd he
    change IsLocalRing.maximalIdeal R ≤ J
    exact (le_of_eq hgen).trans hs

#print axioms s2e_maximalIdeal_generators_stable_mod_square
end HodgeLean.Foundations.Program
