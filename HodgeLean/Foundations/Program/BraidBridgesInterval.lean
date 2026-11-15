import HodgeLean.Foundations.Program.BraidBridgesPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

theorem b65x_bernstein_interval_eval_pos (p : ℚ[X]) (a b : ℚ) (hab : a < b)
    (n : ℕ) (c : Fin (n + 1) → ℚ)
    (hid : ∀ x : ℝ, (p.comp (C a + C (b - a) * X)).eval₂ (Rat.castHom ℝ) x =
      (b65x_bernsteinExpansion n c).eval₂ (Rat.castHom ℝ) x)
    (hc : ∀ i, 0 < c i) (t : ℝ) (ht : t ∈ Set.Icc (a : ℝ) b) :
    0 < p.eval₂ (Rat.castHom ℝ) t := by
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab'
  let x : ℝ := (t - a) / ((b : ℝ) - a)
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hd.le
    · exact (div_le_one hd).mpr (by linarith [ht.2])
  have he : (a : ℝ) + (b - a : ℚ) * x = t := by
    push_cast
    dsimp [x]
    field_simp
    <;> ring
  have h := hid x
  rw [Polynomial.eval₂_comp] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Rat.coe_castHom] at h
  rw [he] at h
  rw [h]
  exact b65x_bernsteinExpansion_pos n c hc x hx

end HodgeLean.Foundations.Program
