import HodgeLean.Foundations.Program.BraidBridgesBernstein

noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

abbrev b65x_CPoly := ℚ[X] × ℚ[X]

def b65x_cpConst (a b : ℚ) : b65x_CPoly := (C a, C b)
def b65x_cpAdd (p q : b65x_CPoly) : b65x_CPoly := (p.1 + q.1, p.2 + q.2)
def b65x_cpSub (p q : b65x_CPoly) : b65x_CPoly := (p.1 - q.1, p.2 - q.2)
def b65x_cpScale (a : ℚ) (p : b65x_CPoly) : b65x_CPoly := (C a * p.1, C a * p.2)
def b65x_cpMul (p q : b65x_CPoly) : b65x_CPoly :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)
def b65x_cpPow (p : b65x_CPoly) : ℕ → b65x_CPoly
  | 0 => b65x_cpConst 1 0
  | n + 1 => b65x_cpMul (b65x_cpPow p n) p

def b65x_cpEval (p : b65x_CPoly) (t : ℝ) : ℂ :=
  ((p.1.eval₂ (Rat.castHom ℝ) t : ℝ) : ℂ) +
    ((p.2.eval₂ (Rat.castHom ℝ) t : ℝ) : ℂ) * Complex.I

def b65x_cpNorm (p : b65x_CPoly) : ℚ[X] := p.1 ^ 2 + p.2 ^ 2

theorem b65x_cpEval_const (a b : ℚ) (t : ℝ) :
    b65x_cpEval (b65x_cpConst a b) t = (a : ℂ) + (b : ℂ) * Complex.I := by
  simp [b65x_cpEval, b65x_cpConst]

theorem b65x_cpEval_add (p q : b65x_CPoly) (t : ℝ) :
    b65x_cpEval (b65x_cpAdd p q) t = b65x_cpEval p t + b65x_cpEval q t := by
  simp [b65x_cpEval, b65x_cpAdd]
  ring

theorem b65x_cpEval_sub (p q : b65x_CPoly) (t : ℝ) :
    b65x_cpEval (b65x_cpSub p q) t = b65x_cpEval p t - b65x_cpEval q t := by
  simp [b65x_cpEval, b65x_cpSub]
  ring

theorem b65x_cpEval_scale (a : ℚ) (p : b65x_CPoly) (t : ℝ) :
    b65x_cpEval (b65x_cpScale a p) t = (a : ℂ) * b65x_cpEval p t := by
  simp [b65x_cpEval, b65x_cpScale]
  ring

theorem b65x_cpEval_mul (p q : b65x_CPoly) (t : ℝ) :
    b65x_cpEval (b65x_cpMul p q) t = b65x_cpEval p t * b65x_cpEval q t := by
  simp [b65x_cpEval, b65x_cpMul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem b65x_cpEval_pow (p : b65x_CPoly) (n : ℕ) (t : ℝ) :
    b65x_cpEval (b65x_cpPow p n) t = b65x_cpEval p t ^ n := by
  induction n with
  | zero => simp [b65x_cpPow, b65x_cpEval_const]
  | succ n ih => rw [b65x_cpPow, b65x_cpEval_mul, ih, pow_succ]

theorem b65x_cpNorm_eval (p : b65x_CPoly) (t : ℝ) :
    (b65x_cpNorm p).eval₂ (Rat.castHom ℝ) t =
      (b65x_cpEval p t).re ^ 2 + (b65x_cpEval p t).im ^ 2 := by
  simp [b65x_cpNorm, b65x_cpEval, Polynomial.eval₂_pow]

theorem b65x_cpEval_ne_zero (p : b65x_CPoly) (t : ℝ)
    (h : 0 < (b65x_cpNorm p).eval₂ (Rat.castHom ℝ) t) :
    b65x_cpEval p t ≠ 0 := by
  intro he
  rw [b65x_cpNorm_eval, he] at h
  norm_num at h

theorem b65x_regular_of_homogeneous (N D : ℂ) (hD : D ≠ 0) (hN : N ≠ 0)
    (h3 : N - 3 * D ≠ 0) (h1 : N - D ≠ 0) (h2 : N + 2 * D ≠ 0)
    (h5 : N ^ 2 * (N - 3 * D) ^ 4 - 5 * (N - D) ^ 3 * (N + 2 * D) ^ 3 ≠ 0)
    (h7 : N ^ 2 * (N - 3 * D) ^ 4 - (-7) * (N - D) ^ 3 * (N + 2 * D) ^ 3 ≠ 0) :
    N / D ∈ b65s_regular := by
  have havoid (c : ℂ) (h : N - c * D ≠ 0) : N / D ≠ c := by
    intro he
    apply h
    rw [div_eq_iff hD] at he
    linear_combination he
  have hpoly (ε : ℂ)
      (hp : N ^ 2 * (N - 3 * D) ^ 4 - ε * (N - D) ^ 3 * (N + 2 * D) ^ 3 ≠ 0) :
      b65r_P ε (N / D) ≠ 0 := by
    intro hz
    apply hp
    unfold b65r_P at hz
    field_simp [hD] at hz
    linear_combination hz
  refine ⟨div_ne_zero hN hD, havoid 3 h3, ?_, ?_, hpoly 5 h5, hpoly (-7) h7⟩
  · apply havoid 1
    simpa using h1
  · apply havoid (-2)
    simpa using h2

end HodgeLean.Foundations.Program
