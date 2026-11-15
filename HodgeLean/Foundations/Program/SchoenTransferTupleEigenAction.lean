import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A common coordinate eigenvalue determines the action of every cyclic deck tuple. -/
theorem s4_tuple_eigen_action {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    (m : ℕ) [NeZero m] (ρ : Multiplicative (I → ZMod m) →* Module.End K V)
    (z : V) (r : K)
    (hz : ∀ i, ρ (.ofAdd (Pi.single i 1)) z = r • z) (v : I → ZMod m) :
    ρ (.ofAdd v) z = r ^ (∑ i, (v i).val) • z := by
  classical
  have hp (i : I) (k : ℕ) : (ρ (.ofAdd (Pi.single i 1)) ^ k) z = r ^ k • z := by
    induction k with
    | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hz i, smul_smul, pow_succ']
      rw [mul_comm]
  have hs (i : I) : ρ (.ofAdd (Pi.single i (v i))) z = r ^ (v i).val • z := by
    have he : (Pi.single i (v i) : I → ZMod m) = (v i).val • (Pi.single i 1) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same, Pi.smul_apply, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      · simp only [Pi.single_eq_of_ne hji, Pi.smul_apply, smul_zero]
    rw [he, ofAdd_nsmul, map_pow, hp]
  have hfin (s : Finset I) :
      ρ (.ofAdd (∑ i ∈ s, Pi.single i (v i))) z = r ^ (∑ i ∈ s, (v i).val) • z := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, ofAdd_zero, map_one, Module.End.one_apply, pow_zero, one_smul]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ofAdd_add, map_mul,
        Module.End.mul_apply, ih, map_smul, hs i, smul_smul, pow_add]
      rw [mul_comm]
  have he : (∑ i, Pi.single i (v i)) = v := by
    ext j
    simp
  simpa only [he] using hfin Finset.univ

/-- A root-of-unity common character is trivial on every sum-zero tuple. -/
theorem s4_sum_zero_tuple_eigen_fixed {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    (m : ℕ) [NeZero m] (ρ : Multiplicative (I → ZMod m) →* Module.End K V)
    (z : V) (r : K) (hr : r ^ m = 1)
    (hz : ∀ i, ρ (.ofAdd (Pi.single i 1)) z = r • z)
    (v : I → ZMod m) (hv : ∑ i, v i = 0) : ρ (.ofAdd v) z = z := by
  rw [s4_tuple_eigen_action m ρ z r hz v]
  have hcast : ((∑ i, (v i).val : ℕ) : ZMod m) = 0 := by
    simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using hv
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  rw [hk, pow_mul, hr, one_pow, one_smul]

end HodgeLean.Foundations.Program
