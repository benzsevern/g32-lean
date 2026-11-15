import Mathlib

/-! # Root counts in discs and exact Gaussian-rational Taylor data

Mathlib-only definitions: the number of roots of a complex polynomial in an open disc,
counted with multiplicity, and the exact rational arithmetic used by the Pellet tests of
the B65-BRAIDCERT checker, part A. Gaussian rationals are pairs `(re, im)` over `ℚ`.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

open Polynomial

open Classical in
/-- Number of roots of `p` in the open disc `D(c, r)`, counted with multiplicity.
Source: Ahlfors, *Complex Analysis*, 3rd ed., §5.2.3 (counting zeros with multiplicity);
Mathlib `Polynomial.roots`. -/
def rou_discCount (p : ℂ[X]) (c : ℂ) (r : ℝ) : ℕ :=
  Multiset.card (p.roots.filter (· ∈ Metric.ball c r))

example : rou_discCount 0 0 1 = 0 := by simp [rou_discCount]

/-- Sum of `‖a_k‖ r^k` over the coefficients of `p` re-centred at `c`, omitting index `m`.
Source: Pellet, *Bull. Sci. Math.* (2) 5 (1881), 393–395; Marden, *Geometry of
Polynomials*, 2nd ed., §27. -/
def rou_pelletTail (p : ℂ[X]) (c : ℂ) (r : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range ((taylor c p).natDegree + 1)).erase m,
    ‖(taylor c p).coeff k‖ * r ^ k

example : rou_pelletTail 0 0 1 1 = 0 := by simp [rou_pelletTail]

/-- Coefficients, constant term first, of `s²(s−3)⁴ − ε(s−1)³(s+2)³`.
Source: G32 v0.16, §5.2, P₅ and P₋₇; expansion of `(s²+s−2)³`. -/
def rou_sextic (ε : ℚ) : Fin 7 → ℚ :=
  ![8 * ε, -12 * ε, 81 - 6 * ε, -108 + 11 * ε, 54 + 3 * ε, -12 - 3 * ε, 1 - ε]

example : rou_sextic 5 0 = 40 := by norm_num [rou_sextic]

/-- Powers of the Gaussian rational `a + b i`, as `(re, im)`.
Source: B65-BRAIDCERT checker part A, `subst(P, s, c + yy)` over `ℚ(i)`. -/
def rou_gpow (a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => ((rou_gpow a b n).1 * a - (rou_gpow a b n).2 * b,
      (rou_gpow a b n).1 * b + (rou_gpow a b n).2 * a)

example : rou_gpow 0 1 2 = (-1, 0) := by norm_num [rou_gpow]

/-- Coefficient of `y^k` in `q(a + b i + y)`, for `q` with coefficients `q 0, …, q 6`,
namely `∑ⱼ q j · C(j, k) · (a + b i)^(j − k)`.
Source: B65-BRAIDCERT checker part A, `polcoef(subst(P, s, c + yy), k, yy)`. -/
def rou_shift (q : Fin 7 → ℚ) (a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  ∑ j : Fin 7, (q j * ((j : ℕ).choose k : ℚ)) • rou_gpow a b ((j : ℕ) - k)

example : rou_shift (rou_sextic 5) 0 0 0 = (40, 0) := by
  simp [rou_shift, rou_sextic, Fin.sum_univ_succ, rou_gpow]; norm_num

/-- The rational majorant `|re z| + |im z|` of the modulus.
Source: B65-BRAIDCERT checker part A, `ab`. -/
def rou_l1 (z : ℚ × ℚ) : ℚ := |z.1| + |z.2|

example : rou_l1 (3, -4) = 7 := by norm_num [rou_l1]

/-- The squared modulus `re² + im²`.
Source: B65-BRAIDCERT checker part A, `norm`. -/
def rou_normSq (z : ℚ × ℚ) : ℚ := z.1 ^ 2 + z.2 ^ 2

example : rou_normSq (3, -4) = 25 := by norm_num [rou_normSq]

/-- Rational Pellet tail `∑_{k ≤ 6, k ≠ m} (|re a_k| + |im a_k|) ρ^k` of the re-centred
sextic data.
Source: B65-BRAIDCERT checker part A, `pellet1` and `pellet0` (multiplied through by `ρ`). -/
def rou_ratTail (q : Fin 7 → ℚ) (a b ρ : ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ (Finset.range 7).erase m, rou_l1 (rou_shift q a b k) * ρ ^ k

example : rou_ratTail (rou_sextic 5) 0 0 0 1 = 40 := by
  simp [rou_ratTail, rou_shift, rou_sextic, Finset.sum_range_succ, Fin.sum_univ_succ,
    rou_gpow, rou_l1]; norm_num

end HodgeLean.Foundations.Program
