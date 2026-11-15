import Mathlib.Algebra.Ring.GeomSum
import HodgeLean.Foundations.QuotientDuality.PersistenceLinear
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Character signs in inverse orbit sums. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_shifted_power_sum {R : Type*} [Ring R] (A : R) (m : ℕ)
    (hA : A ^ m = 1) :
    A * (∑ t : Fin m, A ^ (m - t.val)) = ∑ t : Fin m, A ^ (m - t.val) := by
  have hreflect : (∑ t : Fin m, A ^ (m - t.val)) =
      ∑ i ∈ Finset.range m, A ^ (i + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => A ^ (m - i)) m]
    rw [← Finset.sum_range_reflect (fun i => A ^ (i + 1)) m]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have := Finset.mem_range.mp hi
    omega
  rw [hreflect]
  have hgeom : A * (∑ i ∈ Finset.range m, A ^ i) = ∑ i ∈ Finset.range m, A ^ i := by
    have h := mul_geom_sum A m
    rw [hA, sub_self, sub_mul, one_mul, sub_eq_zero] at h
    exact h
  have hs : (∑ i ∈ Finset.range m, A ^ (i + 1)) =
      A * ∑ i ∈ Finset.range m, A ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact pow_succ' A i
  rw [hs, hgeom, hgeom]

lemma persistence_inverse_weight_sum {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (T : Module.End K V)
    (m : ℕ) [NeZero m] (hT : T ^ m = 1) (ζ : K) (hζ : ζ ^ m = 1) (c : V) :
    ζ • T (∑ t : Fin m, ζ ^ (-(t.val : ZMod m)).val • (T ^ (m - t.val)) c) =
      ∑ t : Fin m, ζ ^ (-(t.val : ZMod m)).val • (T ^ (m - t.val)) c := by
  have hcoeff (t : Fin m) : ζ ^ (-(t.val : ZMod m)).val = ζ ^ (m - t.val) := by
    rw [ZMod.neg_val', ZMod.val_natCast, Nat.mod_eq_of_lt t.isLt]
    exact (pow_eq_pow_mod _ hζ).symm
  simp_rw [hcoeff]
  have hp : (ζ • T) ^ m = (1 : Module.End K V) := by
    rw [smul_pow, hζ, hT, one_smul]
  have h := LinearMap.congr_fun (persistence_shifted_power_sum (ζ • T) m hp) c
  simpa only [smul_pow, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply] using h

lemma persistence_opposite_eigen_no_preimage {K U V : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (S : Module.End K U) (T : Module.End K V) (f : U →ₗ[K] V)
    (hf : ∀ u, T (f u) = f (S u))
    (m : ℕ) (hm : 3 ≤ m) (ζ : K) (hζ : IsPrimitiveRoot ζ m)
    (v : V) (hv : v ≠ 0) (hinv : ζ • T v = v) :
    ¬ ∃ u : U, S u = ζ • u ∧ f u = v := by
  rintro ⟨u, hu, hfu⟩
  have he : T v = ζ • v := by rw [← hfu, hf, hu, map_smul]
  have hs : (ζ ^ 2 - 1) • v = 0 := by
    rw [sub_smul, pow_two, mul_smul, ← he, hinv, one_smul, sub_self]
  rcases smul_eq_zero.mp hs with hs | hs
  · exact (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)) (sub_eq_zero.mp hs)
  · exact hv hs

end HodgeLean.Foundations.QuotientDuality
