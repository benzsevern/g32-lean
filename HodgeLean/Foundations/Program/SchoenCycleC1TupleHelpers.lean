import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # Translation sums for tuples in free fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A permutation and coordinate translations fixing a tuple in free orbit
fibres have total translation zero. -/
theorem s2e_c1_free_tuple_sum_zero
    {I G A B : Type*} [Fintype I] [AddCommGroup G] [AddAction G A]
    (p : A → B) (hp : ∀ (g : G) (a : A), p (g +ᵥ a) = p a)
    (htrans : ∀ a b, p a = p b → ∃ g : G, g +ᵥ a = b)
    (x : I → A) (hfree : ∀ i, Function.Injective (fun g : G => g +ᵥ x i))
    (τ : Equiv.Perm I) (c : I → G)
    (hfix : ∀ i, c i +ᵥ x (τ.symm i) = x i) : ∑ i, c i = 0 := by
  classical
  let J := Set.range (fun i => p (x i))
  choose rep hrep using (fun b : J => b.property)
  let j (i : I) : J := ⟨p (x i), ⟨i, rfl⟩⟩
  have hgex (i : I) : ∃ g : G, g +ᵥ x (rep (j i)) = x i :=
    htrans _ _ (hrep (j i))
  choose g hg using hgex
  have hj (i : I) : j (τ.symm i) = j i := by
    apply Subtype.ext
    change p (x (τ.symm i)) = p (x i)
    exact (hp (c i) (x (τ.symm i))).symm.trans (congrArg p (hfix i))
  have hc (i : I) : c i + g (τ.symm i) = g i := by
    apply hfree (rep (j i))
    calc
      (c i + g (τ.symm i)) +ᵥ x (rep (j i)) =
          c i +ᵥ (g (τ.symm i) +ᵥ x (rep (j (τ.symm i)))) := by
        rw [add_vadd, hj i]
      _ = c i +ᵥ x (τ.symm i) := congrArg (fun z => c i +ᵥ z) (hg (τ.symm i))
      _ = x i := hfix i
      _ = g i +ᵥ x (rep (j i)) := (hg i).symm
  have hs : (∑ i, c i) + ∑ i, g i = ∑ i, g i := by
    calc
      (∑ i, c i) + ∑ i, g i = (∑ i, c i) + ∑ i, g (τ.symm i) := by
        rw [Equiv.sum_comp τ.symm]
      _ = ∑ i, (c i + g (τ.symm i)) := Finset.sum_add_distrib.symm
      _ = ∑ i, g i := Finset.sum_congr rfl (fun i _ => hc i)
  exact add_right_cancel (hs.trans (zero_add _).symm)

/-- Excluding every shorter return makes the degree-indexed periodic orbit
injective. -/
theorem s2e_c1_periodic_orbit_injective {A : Type*} (f : A → A) (z : A)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt f m z)
    (hreturn : ∀ n, n < m → f^[n] z = z → n = 0) :
    Function.Injective (fun t : Fin m => f^[t.val] z) := by
  have hle : Function.minimalPeriod f z ≤ m := hperiod.minimalPeriod_le hm
  have hpos : 0 < Function.minimalPeriod f z := hperiod.minimalPeriod_pos hm
  have hge : m ≤ Function.minimalPeriod f z := by
    by_contra h
    have hzero := hreturn _ (Nat.lt_of_not_ge h) (Function.iterate_minimalPeriod)
    exact (Nat.ne_of_gt hpos) hzero
  have heq : Function.minimalPeriod f z = m := le_antisymm hle hge
  intro t u htu
  apply Fin.ext
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod ?_ ?_).mp htu
  · rw [heq]
    exact t.isLt
  · rw [heq]
    exact u.isLt

end HodgeLean.Foundations.Program
