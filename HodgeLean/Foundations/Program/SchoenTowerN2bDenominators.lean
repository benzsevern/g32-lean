import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finitely many localized elements have representatives with a common exponent. -/
theorem n2b_common_localization_exponent {ι : Type} [Fintype ι]
    (R A : ι → Type) [∀ i, CommRing (R i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra (R i) (A i)] (s : ∀ i, R i)
    [∀ i, IsLocalization.Away (s i) (A i)] (z : ∀ i, A i) :
    ∃ N : ℕ, ∀ i, ∃ a : R i,
      z i * algebraMap (R i) (A i) (s i) ^ N = algebraMap (R i) (A i) a := by
  classical
  have h : ∀ i, ∃ (n : ℕ) (a : R i),
      z i * algebraMap (R i) (A i) (s i) ^ n = algebraMap (R i) (A i) a :=
    fun i => IsLocalization.Away.surj (s i) (z i)
  choose n a ha using h
  let N := Finset.univ.sup n
  refine ⟨N, fun i => ⟨a i * s i ^ (N - n i), ?_⟩⟩
  have hn : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  calc
    z i * algebraMap (R i) (A i) (s i) ^ N =
        z i * (algebraMap (R i) (A i) (s i) ^ n i *
          algebraMap (R i) (A i) (s i) ^ (N - n i)) := by
      rw [← pow_add, Nat.add_sub_of_le hn]
    _ = algebraMap (R i) (A i) (a i * s i ^ (N - n i)) := by
      rw [← mul_assoc, ha, map_mul, map_pow]

end HodgeLean.Foundations.Program
