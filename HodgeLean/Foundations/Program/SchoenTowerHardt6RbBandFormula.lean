import HodgeLean.Foundations.Program.SchoenTowerHardt1Cells

/-! Boolean syntax for the interpolation relation on polynomial bands. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_band_relation {n N : ℕ}
    (f : s2v_t11b_Formula n) (a b c d : MvPolynomial (Fin n) ℝ)
    (idx : Fin n → Fin N) (iy iv : Fin N) :
    ∃ g : s2v_t11b_Formula N, ∀ z,
      z ∈ g.realize ↔
        WithLp.toLp 2 (fun i => z (idx i)) ∈ f.realize ∧
        MvPolynomial.eval (fun i => z (idx i)) a ≤ z iy ∧
        z iy ≤ MvPolynomial.eval (fun i => z (idx i)) b ∧
        MvPolynomial.eval (fun i => z (idx i)) c ≤ z iv ∧
        z iv ≤ MvPolynomial.eval (fun i => z (idx i)) d ∧
        (z iy - MvPolynomial.eval (fun i => z (idx i)) a) *
            (MvPolynomial.eval (fun i => z (idx i)) d -
              MvPolynomial.eval (fun i => z (idx i)) c) =
          (z iv - MvPolynomial.eval (fun i => z (idx i)) c) *
            (MvPolynomial.eval (fun i => z (idx i)) b -
              MvPolynomial.eval (fun i => z (idx i)) a) := by
  let A := MvPolynomial.rename idx a
  let B := MvPolynomial.rename idx b
  let C := MvPolynomial.rename idx c
  let D := MvPolynomial.rename idx d
  let Y : MvPolynomial (Fin N) ℝ := MvPolynomial.X iy
  let V : MvPolynomial (Fin N) ℝ := MvPolynomial.X iv
  let R := (Y - A) * (D - C) - (V - C) * (B - A)
  let g : s2v_t11b_Formula N := .inter (s2v_hardt1_rename idx f)
    (.inter (.nonneg (Y - A)) (.inter (.nonneg (B - Y))
      (.inter (.nonneg (V - C)) (.inter (.nonneg (D - V))
        (.inter (.nonneg R) (.nonneg (-R)))))))
  refine ⟨g, ?_⟩
  intro z
  change (z ∈ (s2v_hardt1_rename idx f).realize ∧
    0 ≤ MvPolynomial.eval (fun i => z i) (Y - A) ∧
    0 ≤ MvPolynomial.eval (fun i => z i) (B - Y) ∧
    0 ≤ MvPolynomial.eval (fun i => z i) (V - C) ∧
    0 ≤ MvPolynomial.eval (fun i => z i) (D - V) ∧
    0 ≤ MvPolynomial.eval (fun i => z i) R ∧
    0 ≤ MvPolynomial.eval (fun i => z i) (-R)) ↔ _
  rw [s2v_hardt1_realize_rename]
  simp only [A, B, C, D, Y, V, R, map_sub, map_mul, map_neg,
    MvPolynomial.eval_X, MvPolynomial.eval_rename, Function.comp_def]
  constructor
  · rintro ⟨hf, ha, hb, hc, hd, hR, hnR⟩
    exact ⟨hf, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hf, ha, hb, hc, hd, hR⟩
    exact ⟨hf, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩

end HodgeLean.Foundations.Program
