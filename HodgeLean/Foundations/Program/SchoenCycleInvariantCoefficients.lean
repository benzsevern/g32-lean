import HodgeLean.Foundations.Program.SchoenCycleInvariantIdealContraction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Averaging coefficients of invariant generators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An invariant element in a finite span of invariant generators has
invariant coefficients.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1,
the averaging projection in characteristic zero. -/
theorem s2e_invariant_span_invariant_coefficients
    (A G ι : Type*) [CommRing A] [Algebra ℂ A] [Group G] [Fintype G] [Fintype ι]
    (a : G →* (A ≃ₐ[ℂ] A)) (c : ι → A) (hc : ∀ g i, a g (c i) = c i)
    (z : A) (hz : ∀ g, a g z = z) (hmem : z ∈ Ideal.span (Set.range c)) :
    ∃ b : ι → A, (∀ g i, a g (b i) = b i) ∧ ∑ i, b i * c i = z := by
  classical
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hmem
  simp only [smul_eq_mul] at hb
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let v : A := algebraMap ℂ A ((Fintype.card G : ℂ)⁻¹)
  let av (x : A) := v * ∑ g : G, a g x
  have hv : v * (Fintype.card G : A) = 1 := by
    dsimp only [v]
    rw [← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hfix (x : A) (g : G) : a g (av x) = av x := by
    dsimp only [av, v]
    rw [map_mul, (a g).commutes, map_sum]
    congr 1
    simp only [← AlgEquiv.mul_apply, ← map_mul]
    rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => a h x)]
  have hm (x : A) (i : ι) : av (x * c i) = av x * c i := by
    simp only [av, map_mul, hc, ← Finset.sum_mul, mul_assoc]
  have hs (d : ι → A) : av (∑ i, d i) = ∑ i, av (d i) := by
    simp only [av, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
  refine ⟨fun i => av (b i), fun g i => hfix (b i) g, ?_⟩
  simp_rw [← hm]
  rw [← hs, hb]
  simp only [av, hz, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, hv, one_mul]

#print axioms s2e_invariant_span_invariant_coefficients
end HodgeLean.Foundations.Program
