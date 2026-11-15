import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Normalizing two nonzero factors recovers them from their rank-one product.
Source: Hartshorne, Algebraic Geometry, Exercise II.5.11. -/
theorem b54_rankOne_normalize {ι κ : Type*} (v x : ι → ℂ) (w y : κ → ℂ)
    (i : ι) (j : κ) (hv : v i = 1) (hw : w j = 1) (c : ℂ)
    (h : ∀ k l, v k * w l = c * (x k * y l)) :
    x i ≠ 0 ∧ y j ≠ 0 ∧ (∀ k, v k = x k / x i) ∧ (∀ l, w l = y l / y j) := by
  have hij : c * (x i * y j) = 1 := by simpa [hv, hw] using (h i j).symm
  have hx : x i ≠ 0 := by intro he; simp [he] at hij
  have hy : y j ≠ 0 := by intro he; simp [he] at hij
  refine ⟨hx, hy, fun k => ?_, fun l => ?_⟩
  · apply (eq_div_iff hx).mpr
    have hk : v k = c * (x k * y j) := by simpa [hw] using h k j
    rw [hk]
    calc
      _ = x k * (c * (x i * y j)) := by ring
      _ = x k := by rw [hij, mul_one]
  · apply (eq_div_iff hy).mpr
    have hl : w l = c * (x i * y l) := by simpa [hv] using h i l
    rw [hl]
    calc
      _ = y l * (c * (x i * y j)) := by ring
      _ = y l := by rw [hij, mul_one]

end HodgeLean.Foundations.Program
