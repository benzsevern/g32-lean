import HodgeLean.Foundations.AnalyticDivisorAlgebraic4Proofs

/-! # Weierstrass preparation and division: frozen specification (Chow/GAGA, fourth stage)

Toward `LefschetzOneOneHyp` for abelian `X` through the Appell--Humbert line bundle `L(H, χ)`:
(a) the line bundle with theta-function sections, (b) the analytic divisor of a section,
(c) Chow/GAGA, (d) the cycle class of that divisor is `c₁`. The third stage
(`HodgeLean.Foundations.AnalyticDivisorAlgebraic3`) proved the regular-point structure of a
hypersurface, orders along lines and chart independence, and recommended this stage (b4):
convergent Weierstrass preparation and division, by root counting with the argument principle.

Coordinates are `ℂⁿ × ℂ = (Fin n → ℂ) × ℂ`, `(z, w)`, with sup norms, so `closedBall z₀ δ ×ˢ
closedBall c r` is a closed polydisc. `monicInLast a` is `(z, w) ↦ w ^ d + ∑_{j < d} a_j(z) w ^ j`
and `zeroCount g c r` counts the zeros of `g` in `ball c r` with multiplicity
(`HodgeLean.Foundations.AnalyticDivisorAlgebraic4Defs`).

Claimed:
* the argument principle in one variable, with an analytic weight: for `g` analytic near the
  closed disc and nonvanishing on its boundary circle, `∮ h g'/g = 2πi ∑ ord_a(g) h(a)` over the
  zeros in the open disc, and `∮ g'/g = 2πi · zeroCount g c r`; falsification: with a zero on the
  circle the identity fails (`w (w - 1)` on the unit circle);
* the analytic order of a polynomial function at a point is its root multiplicity;
* the number of zeros of `w ↦ f (z, w)` in a disc is constant in `z` while no zero crosses the
  boundary circle; at a point where `w ↦ f (z₀, w)` has order `d` at `w₀`, arbitrarily small
  radii `r` and some `δ` make the count equal to `d` for all `z` in `ball z₀ δ`;
* circle integrals of a function analytic in a finite-dimensional parameter are analytic in the
  parameter; the coefficients of `∏ (X - α)` over a family of multisets of size `d` are analytic
  when the power sums of orders `1, …, d` are;
* from these: the monic polynomial in `w` with the same zeros and orders as `f (z, ·)` in the disc
  has coefficients analytic in `z`; and `f = u · P` with `u` analytic on the open polydisc when
  the orders of `P (z, ·)` are at most those of `f (z, ·)` and `P` has no zero on the boundary;
* **Weierstrass preparation** at `0` (`f = u · P`, `u` a unit, `P` a Weierstrass polynomial of
  degree the order of `f (0, ·)` at `0`) and **Weierstrass division** by a Weierstrass polynomial,
  with uniqueness of quotient and remainder; the degree of any preparation is that order;
  falsification: `f (z, w) = z₁`, whose restriction to the `w`-axis vanishes identically, has no
  preparation; the roots of a Weierstrass polynomial tend to `0` with `z`.

Not claimed: uniqueness of the preparation, the ring of germs being Noetherian or a UFD, local
factorization into irreducible Weierstrass polynomials, the discriminant locus, the local
parametrization of a hypersurface, multiplicities at a point or along components, closed
analyticity of the theta divisor in `X(ℂ)`, Chow's theorem or GAGA, algebraicity of any divisor,
or any cycle class. The route and stage estimates are in `docs/specs/AnalyticDivisorAlgebraic4.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Metric Complex

open scoped Real

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic4

section ArgumentPrinciple

/-- **Argument principle with an analytic weight.**  Let `g` and `h` be analytic on a
neighbourhood of the closed disc `closedBall c r`, `r > 0`, with `g` nonvanishing on the circle
`sphere c r`. Then `∮_{|w - c| = r} h(w) g'(w) / g(w) dw = 2πi ∑_a ord_a(g) h(a)`, the sum over the
(finitely many) zeros `a` of `g` in the open disc, with their orders.

Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §5.2, Theorem 18 (the argument principle,
in the form with a weight `h`); Gunning--Rossi, *Analytic Functions of Several Complex
Variables*, Ch. II, §B, proof of Theorem 2; Mathlib's `MeromorphicOn.extract_zeros_poles` and
`DifferentiableOn.circleIntegral_sub_inv_smul`. -/
theorem spec_circleIntegral_mul_logDeriv {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hh : AnalyticOnNhd ℂ h (closedBall c r))
    (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    (∮ w in C(c, r), h w * deriv g w / g w) =
      2 * π * I * ∑ᶠ (a : ℂ) (_ : a ∈ ball c r), (analyticOrderNatAt g a : ℂ) * h a :=
  spec_circleIntegral_mul_logDeriv_aux hr hg hh hne

example {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    (∮ w in C(c, r), (1 : ℂ) * deriv g w / g w) =
      2 * π * I * ∑ᶠ (a : ℂ) (_ : a ∈ ball c r), (analyticOrderNatAt g a : ℂ) * 1 :=
  spec_circleIntegral_mul_logDeriv hr hg (fun _ _ => analyticAt_const) hne

/-- **Argument principle: zero counting.**  For `g` analytic on a neighbourhood of the closed disc
`closedBall c r`, `r > 0`, and nonvanishing on the circle `sphere c r`,
`∮_{|w - c| = r} g'(w) / g(w) dw = 2πi · N`, where `N = zeroCount g c r` is the number of zeros of
`g` in the open disc, counted with multiplicity.

Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §5.2, Theorem 18 (the argument principle). -/
theorem spec_circleIntegral_logDeriv_eq_zeroCount {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    (∮ w in C(c, r), deriv g w / g w) = 2 * π * I * (zeroCount g c r : ℂ) :=
  spec_circleIntegral_logDeriv_eq_zeroCount_aux hr hg hne

example {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hne : ∀ w ∈ sphere c r, g w ≠ 0) :
    ∃ m : ℕ, (∮ w in C(c, r), deriv g w / g w) = 2 * π * I * (m : ℂ) :=
  ⟨_, spec_circleIntegral_logDeriv_eq_zeroCount hr hg hne⟩

/-- **Falsification: the argument principle needs no zero on the circle.**  For
`g w = w (w - 1)` on the unit circle about `0` (a zero at `1` on the circle, one zero `0` inside),
the identity of `spec_circleIntegral_logDeriv_eq_zeroCount` fails: the integrand
`1 / w + 1 / (w - 1)` is not integrable on the circle, so the integral is `0` by convention, while
the right side is `2πi`.

Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §5.2 (the hypothesis that no zero lies on
the contour); Mathlib's `circleIntegrable_sub_inv_iff` and `circleIntegral.integral_undef`. -/
theorem spec_circleIntegral_logDeriv_ne_of_zero_on_sphere :
    (∮ w in C(0, 1), deriv (fun w : ℂ => w * (w - 1)) w / (w * (w - 1))) ≠
      2 * π * I * (zeroCount (fun w : ℂ => w * (w - 1)) 0 1 : ℂ) :=
  spec_circleIntegral_logDeriv_ne_of_zero_on_sphere_aux

example : ¬ ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 1) →
    (∮ w in C(0, 1), deriv g w / g w) = 2 * π * I * (zeroCount g 0 1 : ℂ) :=
  fun H => spec_circleIntegral_logDeriv_ne_of_zero_on_sphere
    (H _ fun _ _ => (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)))

/-- **Analytic order of a polynomial function.**  For a nonzero polynomial `p` over `ℂ` and any
`α`, the analytic order of `w ↦ p(w)` at `α` is the root multiplicity of `α` in `p`.

Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §3.2 (order of a zero); Lang, *Algebra*,
rev. 3rd ed., Ch. IV, §1 (multiplicity of a root); Mathlib's `Polynomial.rootMultiplicity` and
`analyticOrderAt`. -/
theorem spec_analyticOrderAt_polynomial_eval {p : Polynomial ℂ} (hp : p ≠ 0) (α : ℂ) :
    analyticOrderAt (fun w => p.eval w) α = p.rootMultiplicity α :=
  spec_analyticOrderAt_polynomial_eval_aux hp α

example (α : ℂ) :
    analyticOrderAt (fun w => (Polynomial.X - Polynomial.C α).eval w) α = 1 := by
  rw [spec_analyticOrderAt_polynomial_eval (Polynomial.X_sub_C_ne_zero α),
    Polynomial.rootMultiplicity_X_sub_C_self]
  rfl

end ArgumentPrinciple

section Count

variable {n : ℕ}

/-- **Weierstrass radii.**  Let `f : ℂⁿ × ℂ → ℂ` be analytic at `(z₀, w₀)`, with
`w ↦ f (z₀, w)` of finite order `d` at `w₀`. For every `ε > 0` there are `0 < r < ε` and
`δ > 0` such that `f` is analytic on a neighbourhood of the closed polydisc
`closedBall z₀ δ ×ˢ closedBall w₀ r`, has no zero on `closedBall z₀ δ ×ˢ sphere w₀ r`, and
`w ↦ f (z₀, w)` has no zero in `closedBall w₀ r` other than `w₀`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, proof of
Theorem 2 (choice of the polydisc); Hörmander, *An Introduction to Complex Analysis in Several
Variables*, proof of Theorem 6.1.1; Mathlib's `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`. -/
theorem spec_exists_weierstrass_radii {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {w₀ : ℂ}
    {d : ℕ} (hf : AnalyticAt ℂ f (z₀, w₀)) (hd : analyticOrderAt (fun w => f (z₀, w)) w₀ = d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ∃ δ, 0 < δ ∧
      AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall w₀ r) ∧
      (∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere w₀ r, f (z, w) ≠ 0) ∧
      ∀ w ∈ closedBall w₀ r, f (z₀, w) = 0 → w = w₀ :=
  spec_exists_weierstrass_radii_aux hf hd hε

example {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {w₀ : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f (z₀, w₀)) (hd : analyticOrderAt (fun w => f (z₀, w)) w₀ = d) :
    ∃ r, 0 < r ∧ ∀ w ∈ sphere w₀ r, f (z₀, w) ≠ 0 := by
  obtain ⟨r, hr, -, δ, hδ, -, hne, -⟩ := spec_exists_weierstrass_radii hf hd one_pos
  exact ⟨r, hr, hne z₀ (mem_closedBall_self hδ.le)⟩

/-- **The zero count is constant in the parameter.**  Let `f : ℂⁿ × ℂ → ℂ` be analytic on a
neighbourhood of `closedBall z₀ δ ×ˢ closedBall c r`, with no zero on
`closedBall z₀ δ ×ˢ sphere c r`. Then for every `z ∈ ball z₀ δ` the number of zeros of
`w ↦ f (z, w)` in `ball c r`, with multiplicity, equals that of `w ↦ f (z₀, w)`: by the argument
principle it is `(2πi)⁻¹ ∮ ∂_w f / f`, continuous in `z` and integer valued.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, proof of
Theorem 2; Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §5.2 (the argument principle). -/
theorem spec_zeroCount_eq_of_sphere_ne_zero {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {δ : ℝ} {c : ℂ} {r : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, f (z, w) ≠ 0) {z : Fin n → ℂ}
    (hz : z ∈ ball z₀ δ) :
    zeroCount (fun w => f (z, w)) c r = zeroCount (fun w => f (z₀, w)) c r :=
  spec_zeroCount_eq_of_sphere_ne_zero_aux hf hne hz

example {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {δ : ℝ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, f (z, w) ≠ 0) {z z' : Fin n → ℂ}
    (hz : z ∈ ball z₀ δ) (hz' : z' ∈ ball z₀ δ) :
    zeroCount (fun w => f (z, w)) c r = zeroCount (fun w => f (z', w)) c r := by
  rw [spec_zeroCount_eq_of_sphere_ne_zero hf hne hz,
    spec_zeroCount_eq_of_sphere_ne_zero hf hne hz']

/-- **The number of zeros on a small circle is the order.**  Let `f : ℂⁿ × ℂ → ℂ` be analytic at
`(z₀, w₀)`, with `w ↦ f (z₀, w)` of finite order `d` at `w₀`. For every `ε > 0` there are
`0 < r < ε` and `δ > 0` such that `f` is analytic near `closedBall z₀ δ ×ˢ closedBall w₀ r`,
nonvanishing on `closedBall z₀ δ ×ˢ sphere w₀ r`, and for every `z ∈ ball z₀ δ` the function
`w ↦ f (z, w)` has exactly `d` zeros in `ball w₀ r`, counted with multiplicity.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, proof of
Theorem 2; Hörmander, *An Introduction to Complex Analysis in Several Variables*, proof of
Theorem 6.1.1. -/
theorem spec_exists_zeroCount_eq_order {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {w₀ : ℂ} {d : ℕ} (hf : AnalyticAt ℂ f (z₀, w₀))
    (hd : analyticOrderAt (fun w => f (z₀, w)) w₀ = d) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ∃ δ, 0 < δ ∧
      AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall w₀ r) ∧
      (∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere w₀ r, f (z, w) ≠ 0) ∧
      ∀ z ∈ ball z₀ δ, zeroCount (fun w => f (z, w)) w₀ r = d :=
  spec_exists_zeroCount_eq_order_aux hf hd hε

example {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {w₀ : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f (z₀, w₀)) (hd : analyticOrderAt (fun w => f (z₀, w)) w₀ = d) :
    ∃ r > 0, ∃ δ > 0, ∀ z ∈ ball z₀ δ, zeroCount (fun w => f (z, w)) w₀ r = d := by
  obtain ⟨r, hr, -, δ, hδ, -, -, h⟩ := spec_exists_zeroCount_eq_order hf hd one_pos
  exact ⟨r, hr, δ, hδ, h⟩

end Count

section Coefficients

variable {n : ℕ}

/-- **Circle integrals depending analytically on a parameter.**  Let `V` be a finite-dimensional
complex normed space and `F : V × ℂ → ℂ` analytic at every point of `U ×ˢ sphere c r`, `r > 0`.
Then `z ↦ ∮_{|w - c| = r} F (z, w) dw` is analytic at every point of `U`: it is complex
differentiable near each such point (differentiation under the integral), hence analytic by
Osgood's lemma.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 2
(Osgood's lemma) and Ch. II, §B, proof of Theorem 2 (holomorphy of the integrals in the
parameter); with `HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn`. -/
theorem spec_analyticOnNhd_circleIntegral {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {F : V × ℂ → ℂ} {U : Set V} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere c r)) :
    AnalyticOnNhd ℂ (fun z => ∮ w in C(c, r), F (z, w)) U :=
  spec_analyticOnNhd_circleIntegral_aux hr hF

example {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {F : V × ℂ → ℂ} (hF : ∀ p, AnalyticAt ℂ F p) :
    AnalyticOnNhd ℂ (fun z => ∮ w in C(0, 1), F (z, w)) univ :=
  spec_analyticOnNhd_circleIntegral one_pos fun p _ => hF p

/-- **Newton's identities, analytically.**  Let `S z` be a multiset of `d` complex numbers for
each `z` in an open set `U ⊆ ℂⁿ`, such that the power sums `∑_{α ∈ S z} α ^ k`, `1 ≤ k ≤ d`, are
analytic on `U`. Then every coefficient of the monic polynomial `∏_{α ∈ S z} (X - α)` is analytic
on `U`: over `ℂ` the elementary symmetric functions are polynomials in the first `d` power sums.

Source: Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Ch. I, §2, (2.11')
(Newton's identities); Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II,
§B, proof of Theorem 2; Mathlib's `MvPolynomial.mul_esymm_eq_sum` and
`Multiset.prod_X_sub_C_coeff`. -/
theorem spec_analyticOnNhd_coeff_of_powerSum {S : (Fin n → ℂ) → Multiset ℂ}
    {U : Set (Fin n → ℂ)} {d : ℕ} (hU : IsOpen U) (hcard : ∀ z ∈ U, Multiset.card (S z) = d)
    (hpow : ∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((S z).map (· ^ k)).sum) U)
    (j : ℕ) :
    AnalyticOnNhd ℂ
      (fun z => ((S z).map (fun α => Polynomial.X - Polynomial.C α)).prod.coeff j) U :=
  spec_analyticOnNhd_coeff_of_powerSum_aux hU hcard hpow j

example {S : (Fin n → ℂ) → Multiset ℂ} {U : Set (Fin n → ℂ)} {d : ℕ} (hU : IsOpen U)
    (hcard : ∀ z ∈ U, Multiset.card (S z) = d)
    (hpow : ∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((S z).map (· ^ k)).sum) U) :
    ContinuousOn
      (fun z => ((S z).map (fun α => Polynomial.X - Polynomial.C α)).prod.coeff 0) U :=
  (spec_analyticOnNhd_coeff_of_powerSum hU hcard hpow 0).continuousOn

/-- **The polynomial of the zeros has analytic coefficients.**  Let `f : ℂⁿ × ℂ → ℂ` be analytic
on a neighbourhood of `closedBall z₀ δ ×ˢ closedBall c r`, with no zero on
`closedBall z₀ δ ×ˢ sphere c r`, and let `w ↦ f (z₀, w)` have `d` zeros in `ball c r`. Then there
are coefficient functions `a j`, analytic on `ball z₀ δ`, such that for `z ∈ ball z₀ δ` the monic
polynomial `w ^ d + ∑_{j < d} a_j(z) w ^ j` has all its zeros in `ball c r`, and at every point of
`ball c r` the same order as `w ↦ f (z, w)`. Its coefficients are the elementary symmetric
functions of the zeros, obtained from the power sums `(2πi)⁻¹ ∮ w ^ k ∂_w f / f`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, proof of
Theorem 2 (Weierstrass preparation theorem); Hörmander, *An Introduction to Complex Analysis in
Several Variables*, proof of Theorem 6.1.1. -/
theorem spec_exists_monicInLast_orders {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {δ : ℝ} {c : ℂ} {r : ℝ} {d : ℕ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, f (z, w) ≠ 0)
    (hd : zeroCount (fun w => f (z₀, w)) c r = d) :
    ∃ a : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticOnNhd ℂ (a j) (ball z₀ δ)) ∧
      ∀ z ∈ ball z₀ δ, (∀ w, monicInLast a (z, w) = 0 → w ∈ ball c r) ∧
        ∀ w ∈ ball c r, analyticOrderAt (fun w => monicInLast a (z, w)) w =
          analyticOrderAt (fun w => f (z, w)) w :=
  spec_exists_monicInLast_orders_aux hf hne hd

example {f : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {δ : ℝ} {c : ℂ} {r : ℝ} {d : ℕ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, f (z, w) ≠ 0)
    (hd : zeroCount (fun w => f (z₀, w)) c r = d) :
    ∃ a : Fin d → (Fin n → ℂ) → ℂ, ∀ z ∈ ball z₀ δ, ∀ w, monicInLast a (z, w) = 0 →
      w ∈ ball c r := by
  obtain ⟨a, -, h⟩ := spec_exists_monicInLast_orders hf hne hd
  exact ⟨a, fun z hz => (h z hz).1⟩

/-- **Analytic quotients on a polydisc.**  Let `f, P : ℂⁿ × ℂ → ℂ` be analytic on a
neighbourhood of `closedBall z₀ δ ×ˢ closedBall c r`, with `P` nonvanishing on
`closedBall z₀ δ ×ˢ sphere c r`, and suppose that at every point of the open polydisc the order of
`w ↦ P (z, w)` is at most that of `w ↦ f (z, w)`. Then `f = u · P` on the open polydisc
`ball z₀ δ ×ˢ ball c r` for a function `u` analytic there, namely
`u (z, w) = (2πi)⁻¹ ∮_{|ζ - c| = r} f (z, ζ) / (P (z, ζ) (ζ - w)) dζ`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, proof of
Theorem 2 (the quotient `f / P` is holomorphic); Hörmander, *An Introduction to Complex Analysis
in Several Variables*, proof of Theorem 6.1.1. -/
theorem spec_exists_analytic_quotient {f P : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ}
    {δ : ℝ} {c : ℂ} {r : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hP : AnalyticOnNhd ℂ P (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, P (z, w) ≠ 0)
    (hord : ∀ z ∈ ball z₀ δ, ∀ w ∈ ball c r,
      analyticOrderAt (fun w => P (z, w)) w ≤ analyticOrderAt (fun w => f (z, w)) w) :
    ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticOnNhd ℂ u (ball z₀ δ ×ˢ ball c r) ∧
      ∀ p ∈ ball z₀ δ ×ˢ ball c r, f p = u p * P p :=
  spec_exists_analytic_quotient_aux hf hP hne hord

example {f P : (Fin n → ℂ) × ℂ → ℂ} {z₀ : Fin n → ℂ} {δ : ℝ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ δ ×ˢ closedBall c r))
    (hP : AnalyticOnNhd ℂ P (closedBall z₀ δ ×ˢ closedBall c r))
    (hne : ∀ z ∈ closedBall z₀ δ, ∀ w ∈ sphere c r, P (z, w) ≠ 0)
    (hord : ∀ z ∈ ball z₀ δ, ∀ w ∈ ball c r,
      analyticOrderAt (fun w => P (z, w)) w ≤ analyticOrderAt (fun w => f (z, w)) w)
    {p : (Fin n → ℂ) × ℂ} (hp : p ∈ ball z₀ δ ×ˢ ball c r) (hPp : P p = 0) : f p = 0 := by
  obtain ⟨u, -, h⟩ := spec_exists_analytic_quotient hf hP hne hord
  rw [h p hp, hPp, mul_zero]

end Coefficients

section Preparation

variable {n : ℕ}

/-- **Weierstrass preparation theorem (convergent, several variables).**  Let `f : ℂⁿ × ℂ → ℂ` be
analytic at `0`, with `w ↦ f (0, w)` of finite order `d` at `0`. Then near `0`,
`f = u · (w ^ d + ∑_{j < d} a_j(z) w ^ j)` with `u` analytic at `0`, `u 0 ≠ 0`, and each `a j`
analytic at `0` with `a j 0 = 0`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Theorem 2
(Weierstrass preparation theorem); Hörmander, *An Introduction to Complex Analysis in Several
Variables*, Theorem 6.1.1; Mathlib's formal analogue `PowerSeries.exists_isWeierstrassFactorization`
(one variable over a complete local ring). -/
theorem spec_weierstrass_preparation {f : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f 0) (hd : analyticOrderAt (fun w => f (0, w)) 0 = d) :
    ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∃ a : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
        f =ᶠ[𝓝 0] fun p => u p * monicInLast a p :=
  spec_weierstrass_preparation_aux hf hd

example {f : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ} (hf : AnalyticAt ℂ f 0)
    (hd : analyticOrderAt (fun w => f (0, w)) 0 = d) :
    ∃ a : Fin d → (Fin n → ℂ) → ℂ, ∀ᶠ p in 𝓝 0, monicInLast a p = 0 → f p = 0 := by
  obtain ⟨_, -, -, a, -, h⟩ := spec_weierstrass_preparation hf hd
  exact ⟨a, h.mono fun p hp hP => by rw [hp]; simp [hP]⟩

/-- **The degree of a preparation is the order.**  If near `0`, `f = u · (w ^ d + ∑_{j < d}
a_j(z) w ^ j)` with `u` analytic at `0`, `u 0 ≠ 0` and every `a j 0 = 0`, then `w ↦ f (0, w)` has
order exactly `d` at `0`: on the `w`-axis the factor is `w ^ d`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Theorem 2
and Definition 2; Mathlib's `analyticOrderAt_mul` and `analyticOrderAt_congr`. -/
theorem spec_analyticOrderAt_of_preparation {f u : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (ha : ∀ j, a j 0 = 0) (hfu : f =ᶠ[𝓝 0] fun p => u p * monicInLast a p) :
    analyticOrderAt (fun w => f (0, w)) 0 = d :=
  spec_analyticOrderAt_of_preparation_aux hu hu0 ha hfu

example {d : ℕ} :
    analyticOrderAt (fun w => monicInLast (fun _ _ => 0 : Fin d → (Fin n → ℂ) → ℂ) (0, w)) 0
      = d :=
  spec_analyticOrderAt_of_preparation (u := fun _ => 1) analyticAt_const one_ne_zero
    (fun _ => rfl) (Eventually.of_forall fun _ => (one_mul _).symm)

/-- **Falsification: preparation needs finite order on the `w`-axis.**  The coordinate function
`f (z, w) = z₁` on `ℂ¹ × ℂ` is analytic, but `w ↦ f (0, w)` is identically `0` (order `⊤`), and
`f` has no factorization `u · P` with `u` analytic at `0`, `u 0 ≠ 0`, and `P` monic in `w` with
coefficients vanishing at `0`: on the `w`-axis this would give `0 = u (0, w) w ^ d` near `0`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B (the
hypothesis that `f (0, w)` is not identically zero, arranged by a linear change of coordinates);
elementary. -/
theorem spec_not_exists_preparation_coord :
    ¬ ∃ (d : ℕ) (u : (Fin 1 → ℂ) × ℂ → ℂ) (a : Fin d → (Fin 1 → ℂ) → ℂ),
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ (∀ j, a j 0 = 0) ∧
      (fun p : (Fin 1 → ℂ) × ℂ => p.1 0) =ᶠ[𝓝 0] fun p => u p * monicInLast a p :=
  spec_not_exists_preparation_coord_aux

example : ¬ ∃ d : ℕ,
    analyticOrderAt (fun w : ℂ => (((0 : Fin 1 → ℂ), w) : (Fin 1 → ℂ) × ℂ).1 0) 0 = d := by
  rintro ⟨d, hd⟩
  obtain ⟨u, hu, hu0, a, ha, h⟩ := spec_weierstrass_preparation
    (f := fun p : (Fin 1 → ℂ) × ℂ => p.1 0)
    (((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)).analyticAt 0) hd
  exact spec_not_exists_preparation_coord ⟨d, u, a, hu, hu0, fun j => (ha j).2, h⟩

/-- **Roots of a Weierstrass polynomial are small.**  If every coefficient `a j` is continuous at
`0` and vanishes there, then for each `ε > 0` and all `z` near `0`, every root `w` of
`w ^ d + ∑_{j < d} a_j(z) w ^ j` has `‖w‖ < ε`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B (roots of a
Weierstrass polynomial); Marden, *Geometry of Polynomials*, §27 (Cauchy's bound on the roots). -/
theorem spec_monicInLast_roots_small {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, ContinuousAt (a j) 0) (ha0 : ∀ j, a j 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 0, ∀ w, monicInLast a (z, w) = 0 → ‖w‖ < ε :=
  spec_monicInLast_roots_small_aux ha ha0 hε

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, ContinuousAt (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) : ∀ w, monicInLast a (0, w) = 0 → ‖w‖ < 1 :=
  (spec_monicInLast_roots_small ha ha0 one_pos).self_of_nhds

/-- **Weierstrass division theorem (convergent, several variables).**  Let `g : ℂⁿ × ℂ → ℂ` be
analytic at `0`, and `P = w ^ d + ∑_{j < d} a_j(z) w ^ j` with every `a j` analytic at `0` and
`a j 0 = 0`. Then near `0`, `g = q · P + ∑_{j < d} b_j(z) w ^ j` with `q` analytic at `0` and every
`b j` analytic at `0`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Theorem 1
(Weierstrass division theorem); Hörmander, *An Introduction to Complex Analysis in Several
Variables*, Theorem 6.1.2; Mathlib's formal analogue `PowerSeries.exists_isWeierstrassDivision`. -/
theorem spec_weierstrass_division {g : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (hg : AnalyticAt ℂ g 0) (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) :
    ∃ q : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∃ b : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (b j) 0) ∧
        g =ᶠ[𝓝 0] fun p => q p * monicInLast a p + ∑ j, b j p.1 * p.2 ^ (j : ℕ) :=
  spec_weierstrass_division_aux hg ha ha0

example {g : (Fin n → ℂ) × ℂ → ℂ} {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (hg : AnalyticAt ℂ g 0) (ha : ∀ j, AnalyticAt ℂ (a j) 0) (ha0 : ∀ j, a j 0 = 0) :
    ∃ b : Fin d → (Fin n → ℂ) → ℂ,
      ∀ᶠ p in 𝓝 0, monicInLast a p = 0 → g p = ∑ j, b j p.1 * p.2 ^ (j : ℕ) := by
  obtain ⟨_, -, b, -, h⟩ := spec_weierstrass_division hg ha ha0
  exact ⟨b, h.mono fun p hp hP => by rw [hp]; simp [hP]⟩

/-- **Uniqueness in Weierstrass division.**  Let `P = w ^ d + ∑_{j < d} a_j(z) w ^ j` with every
`a j` continuous at `0` and `a j 0 = 0`. If `q · P + ∑_{j < d} b_j(z) w ^ j = 0` near `0` with `q`
analytic at `0`, then `q = 0` near `0` and every `b j = 0` near `0`: for small `z` the remainder,
of degree `< d` in `w`, vanishes at the `d` roots of `P (z, ·)` with multiplicity.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Theorem 1
(uniqueness of `q` and `r`); Hörmander, *An Introduction to Complex Analysis in Several
Variables*, Theorem 6.1.2. -/
theorem spec_weierstrass_division_unique {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, ContinuousAt (a j) 0) (ha0 : ∀ j, a j 0 = 0) {q : (Fin n → ℂ) × ℂ → ℂ}
    (hq : AnalyticAt ℂ q 0) {b : Fin d → (Fin n → ℂ) → ℂ}
    (h : ∀ᶠ p in 𝓝 0, q p * monicInLast a p + ∑ j, b j p.1 * p.2 ^ (j : ℕ) = 0) :
    (∀ᶠ p in 𝓝 0, q p = 0) ∧ ∀ j, ∀ᶠ z in 𝓝 0, b j z = 0 :=
  spec_weierstrass_division_unique_aux ha ha0 hq h

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, ContinuousAt (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) {q : (Fin n → ℂ) × ℂ → ℂ} (hq : AnalyticAt ℂ q 0)
    {b : Fin d → (Fin n → ℂ) → ℂ}
    (h : ∀ᶠ p in 𝓝 0, q p * monicInLast a p + ∑ j, b j p.1 * p.2 ^ (j : ℕ) = 0) :
    q 0 = 0 :=
  (spec_weierstrass_division_unique ha ha0 hq h).1.self_of_nhds

end Preparation

end HodgeLean.Foundations.AnalyticDivisorAlgebraic4
