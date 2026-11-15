import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Invariant representatives of finite quotient jets -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An element congruent modulo an ideal to all its finite-group translates has
a fixed representative. The ideal may define an infinitesimal neighbourhood.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
the averaging operator for a finite group in characteristic zero. -/
theorem s2e_invariant_jet_representative
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (I : Ideal A) (x : A)
    (hx : ∀ g, a g x - x ∈ I) :
    ∃ y : A, (∀ g, a g y = y) ∧ y - x ∈ I := by
  classical
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let v : A := algebraMap ℂ A ((Fintype.card G : ℂ)⁻¹)
  let y : A := v * ∑ g : G, a g x
  have hv : v * (Fintype.card G : A) = 1 := by
    dsimp only [v]
    rw [← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hn, map_one]
  refine ⟨y, ?_, ?_⟩
  · intro g
    dsimp only [y, v]
    rw [map_mul, (a g).commutes, map_sum]
    congr 1
    simp only [← AlgEquiv.mul_apply, ← map_mul]
    rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => a h x)]
  · have he : y - x = v * ∑ g : G, (a g x - x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_sub, ← mul_assoc, hv, one_mul]
    rw [he]
    exact I.mul_mem_left v (I.sum_mem (fun g _ => hx g))

end HodgeLean.Foundations.Program
