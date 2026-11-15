import HodgeLean.Foundations.Program.BraidBridgesDefs
import Mathlib.RingTheory.Polynomial.Bernstein

noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial
open scoped BigOperators

def b65x_bernsteinExpansion (n : ℕ) (c : Fin (n + 1) → ℚ) : ℚ[X] :=
  ∑ i, C (c i) * X ^ i.val * (1 - X) ^ (n - i.val)

theorem b65x_bernsteinExpansion_pos (n : ℕ) (c : Fin (n + 1) → ℚ)
    (hc : ∀ i, 0 < c i) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < (b65x_bernsteinExpansion n c).eval₂ (Rat.castHom ℝ) x := by
  simp only [b65x_bernsteinExpansion, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Rat.coe_castHom]
  have hnonneg (i : Fin (n + 1)) :
      0 ≤ (c i : ℝ) * x ^ i.val * (1 - x) ^ (n - i.val) := by
    have hc' : 0 < (c i : ℝ) := by exact_mod_cast hc i
    exact mul_nonneg (mul_nonneg hc'.le (pow_nonneg hx.1 _))
      (pow_nonneg (sub_nonneg.mpr hx.2) _)
  apply Finset.sum_pos'
  · intro i _; exact hnonneg i
  · by_cases hlt : x < 1
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      have hc' : 0 < (c 0 : ℝ) := by exact_mod_cast hc 0
      simpa only [Fin.val_zero, pow_zero, mul_one, Nat.sub_zero] using
        mul_pos hc' (pow_pos (sub_pos.mpr hlt) n)
    · have hx1 : x = 1 := le_antisymm hx.2 (not_lt.mp hlt)
      refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
      simpa only [hx1, Fin.val_last, one_pow, mul_one, Nat.sub_self, pow_zero] using
        (show 0 < (c (Fin.last n) : ℝ) by exact_mod_cast hc (Fin.last n))

theorem b65x_bernstein_interval_pos (p : ℚ[X]) (a b : ℚ) (hab : a < b)
    (n : ℕ) (c : Fin (n + 1) → ℚ)
    (hid : p.comp (C a + C (b - a) * X) = b65x_bernsteinExpansion n c)
    (hc : ∀ i, 0 < c i) (t : ℝ) (ht : t ∈ Set.Icc (a : ℝ) b) :
    0 < p.eval₂ (Rat.castHom ℝ) t := by
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab'
  let x : ℝ := (t - a) / ((b : ℝ) - a)
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hd.le
    · apply (div_le_one hd).mpr
      linarith [ht.2]
  have he : (a : ℝ) + (b - a : ℚ) * x = t := by
    push_cast
    dsimp [x]
    field_simp
    <;> ring
  have h := congrArg (fun q : ℚ[X] ↦ q.eval₂ (Rat.castHom ℝ) x) hid
  rw [Polynomial.eval₂_comp] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Rat.coe_castHom] at h
  rw [he] at h
  rw [h]
  exact b65x_bernsteinExpansion_pos n c hc x hx

end HodgeLean.Foundations.Program
