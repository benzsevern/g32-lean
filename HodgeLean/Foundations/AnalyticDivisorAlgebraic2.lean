import HodgeLean.Foundations.AnalyticDivisorAlgebraic2Proofs

/-! # Several-variable holomorphy: frozen specification (Chow/GAGA, second stage)

Toward `LefschetzOneOneHyp` for abelian `X` through the Appell--Humbert line bundle `L(H, χ)`:
(a) the line bundle with theta-function sections, (b) the analytic divisor of a section,
(c) Chow/GAGA, (d) the cycle class of that divisor is `c₁`. The first stage
(`HodgeLean.Foundations.AnalyticDivisorAlgebraic`) recommended building (b) next, starting with
Osgood's lemma, the first several-variable analytic input that (b) needs. This stage freezes
Osgood's lemma through the Cauchy integral on polydiscs, and its first consequence for (b).

Claimed:
* the multi-index geometric series: `∑_α ∏ᵢ uᵢ ^ αᵢ = ∏ᵢ (1 - uᵢ)⁻¹` for `‖uᵢ‖ < 1`;
* the Cauchy integral formula on polydiscs `closedBall c r ⊆ ℂⁿ` (sup norm) for a function complex
  differentiable on an open neighbourhood of the polydisc, with Mathlib's `torusIntegral`;
* a Cauchy-type integral over the distinguished boundary of a polydisc, of a function continuous on
  the closed polydisc, is analytic at the centre;
* Osgood's lemma in Fréchet form: a function complex differentiable on an open subset of `ℂⁿ`, or
  of a finite-dimensional complex normed space, with values in a complex Banach space, is analytic
  there;
* the zero set of an entire function on a finite-dimensional complex normed space, in particular of
  a theta function `θ ∈ sections D` in any dimension, is closed analytic;
* falsification for the continuity input of Osgood's lemma over `ℝ`: `xy / (x² + y²)` is analytic
  in each real variable separately and discontinuous at the origin.

Not claimed: Hartogs' theorem (separate holomorphy without continuity), Weierstrass preparation
for convergent power series, the local structure of the zero set of a holomorphic function, orders
of vanishing in several variables, analytic structure on `V ⧸ Λ` or on the theta divisor in
`X(ℂ)`, Chow's theorem or GAGA, algebraicity of any divisor, or any cycle class. The route and
stage estimates are in `docs/specs/AnalyticDivisorAlgebraic2.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Metric Complex

open scoped Real

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic2

open AppellHumbert

/-- **The multi-index geometric series.**  For `u : Fin n → ℂ` with every `‖uᵢ‖ < 1`, the family
`α ↦ ∏ᵢ uᵢ ^ αᵢ` indexed by `α : Fin n → ℕ` is summable with sum `∏ᵢ (1 - uᵢ)⁻¹`. This is the
expansion of the Cauchy kernel on a polydisc.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, proof of
Theorem 2 (expansion of the Cauchy kernel); Mathlib's `hasSum_geometric_of_norm_lt_one`. -/
theorem spec_hasSum_prod_geometric {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    HasSum (fun α : Fin n → ℕ => ∏ i, u i ^ α i) (∏ i, (1 - u i)⁻¹) :=
  spec_hasSum_prod_geometric_aux u hu

example : HasSum (fun α : Fin 2 → ℕ => ∏ i, ((1 : ℂ) / 2) ^ α i) 4 := by
  have h := spec_hasSum_prod_geometric (fun _ : Fin 2 => (1 : ℂ) / 2) fun _ => by
    norm_num
  convert h using 1
  norm_num [Fin.prod_univ_two]

section Polydisc

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Cauchy integral formula on polydiscs.**  Let `f : ℂⁿ → E` be complex differentiable on an
open set `U` containing the closed polydisc `closedBall c r` (sup norm, so this is the product of
the closed discs of radius `r` about the `cᵢ`). For `z` in the open polydisc,
`∯ w in T(c, r), (∏ᵢ (wᵢ - zᵢ))⁻¹ • f w = (2πi)ⁿ • f z`, the integral being over the distinguished
boundary `{w | ∀ i, |wᵢ - cᵢ| = r}`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 2;
Hörmander, *An Introduction to Complex Analysis in Several Variables*, Theorem 2.2.1; Mathlib's
`torusIntegral_succ` and the one-variable
`DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`. -/
theorem spec_torusIntegral_cauchy {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {c : Fin n → ℂ} {r : ℝ}
    (hcU : closedBall c r ⊆ U) {z : Fin n → ℂ} (hz : z ∈ ball c r) :
    (∯ w in T(c, fun _ => r), (∏ i, (w i - z i))⁻¹ • f w) = (2 * π * I) ^ n • f z :=
  spec_torusIntegral_cauchy_aux hU hf hcU hz

example {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f) (c : Fin n → ℂ) :
    (∯ w in T(c, fun _ => 1), (∏ i, (w i - c i))⁻¹ • f w) = (2 * π * I) ^ n • f c :=
  spec_torusIntegral_cauchy isOpen_univ hf.differentiableOn (subset_univ _)
    (mem_ball_self one_pos)

/-- **Cauchy-type integrals are analytic.**  For `f : ℂⁿ → E` continuous on the closed polydisc
`closedBall c r`, `r > 0`, the function `z ↦ ∯ w in T(c, r), (∏ᵢ (wᵢ - zᵢ))⁻¹ • f w` is analytic
at the centre `c`: expanding the kernel by the multi-index geometric series gives a convergent
power series.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, proof of
Theorem 2 (Cauchy integral to power series); Hörmander, *An Introduction to Complex Analysis in
Several Variables*, proof of Theorem 2.2.6. -/
theorem spec_analyticAt_torusCauchyIntegral {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (closedBall c r)) :
    AnalyticAt ℂ (fun z => ∯ w in T(c, fun _ => r), (∏ i, (w i - z i))⁻¹ • f w) c :=
  spec_analyticAt_torusCauchyIntegral_aux hr hf

example (c : Fin n → ℂ) :
    AnalyticAt ℂ (fun z => ∯ w in T(c, fun _ => 1), (∏ i, (w i - z i))⁻¹ • (1 : ℂ)) c :=
  spec_analyticAt_torusCauchyIntegral one_pos continuousOn_const

/-- **Osgood's lemma (Fréchet form) on `ℂⁿ`.**  A function `ℂⁿ → E` into a complex Banach space
that is complex differentiable on an open set `U` is analytic on `U`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 2
(Osgood's lemma) and Definition 1; Hörmander, *An Introduction to Complex Analysis in Several
Variables*, Theorem 2.2.6. -/
theorem spec_analyticOnNhd_of_differentiableOn_fin {f : (Fin n → ℂ) → E}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U :=
  spec_analyticOnNhd_of_differentiableOn_fin_aux hU hf

example : AnalyticOnNhd ℂ (fun z : Fin 2 → ℂ => (z 0 * z 1 - 1)⁻¹) {z | z 0 * z 1 ≠ 1} := by
  refine spec_analyticOnNhd_of_differentiableOn_fin
    (isOpen_ne_fun (by fun_prop) continuous_const) fun z hz => ?_
  have h : z 0 * z 1 - 1 ≠ 0 := sub_ne_zero.2 hz
  have hd : DifferentiableAt ℂ (fun z : Fin 2 → ℂ => z 0 * z 1 - 1) z := by fun_prop
  exact (hd.inv h).differentiableWithinAt

end Polydisc

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Osgood's lemma (Fréchet form).**  On a finite-dimensional complex normed space `V`, a
function into a complex Banach space that is complex differentiable on an open set `U` is
analytic on `U`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 2
(Osgood's lemma), transported along a linear isomorphism `V ≃ ℂⁿ`. -/
theorem spec_analyticOnNhd_of_differentiableOn {f : V → E} {U : Set V} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U :=
  spec_analyticOnNhd_of_differentiableOn_aux hU hf

example {f : V → E} (hf : Differentiable ℂ f) (v : V) : AnalyticAt ℂ f v :=
  spec_analyticOnNhd_of_differentiableOn isOpen_univ hf.differentiableOn v (mem_univ v)

/-- The zero set of an entire function on a finite-dimensional complex normed space `V` is closed
analytic in `V` (charted on itself).

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, Theorem 2
(Osgood's lemma) and Ch. II, §E, Definition 1; with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic.spec_isClosedAnalytic_zeroSet`. -/
theorem spec_isClosedAnalytic_zeroSet_of_differentiable {f : V → ℂ}
    (hf : Differentiable ℂ f) : IsClosedAnalytic V {v | f v = 0} :=
  spec_isClosedAnalytic_zeroSet_of_differentiable_aux hf

example : IsClosedAnalytic (Fin 2 → ℂ) {z : Fin 2 → ℂ | Complex.exp (z 0) - z 1 = 0} :=
  spec_isClosedAnalytic_zeroSet_of_differentiable (by fun_prop)

/-- **Theta divisors are analytic, in every dimension.**  The zero set in `V` of a theta function
`θ ∈ sections D` of an Appell--Humbert datum is closed analytic in `V`. This removes the
genus-one restriction of
`HodgeLean.Foundations.AnalyticDivisorAlgebraic.spec_isClosedAnalytic_theta_genusOne`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §4.1 (theta functions
are holomorphic, their divisors); Gunning--Rossi, *Analytic Functions of Several Complex
Variables*, Ch. I, §A, Theorem 2 (Osgood's lemma). -/
theorem spec_isClosedAnalytic_theta (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) : IsClosedAnalytic V {v | θ v = 0} :=
  spec_isClosedAnalytic_theta_aux D hθ

example (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) :
    IsClosed {v | θ v = 0} :=
  (spec_isClosedAnalytic_theta D hθ).1

end FiniteDimensional

/-- **Falsification for Osgood's continuity input, over `ℝ`.**  The function
`f (x, y) = xy / (x² + y²)` (with `f (0, 0) = 0`) is real analytic in each variable separately on
all of `ℝ`, but it is not continuous at the origin (it is `1/2` on the diagonal). So separate
analyticity does not give joint analyticity without a further input: over `ℂ` this input is
continuity (Osgood) or Hartogs' theorem, and Osgood's lemma above assumes Fréchet complex
differentiability, which includes continuity.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A, remark after
Theorem 2; Krantz, *Function Theory of Several Complex Variables*, 2nd ed., §1.2. -/
theorem spec_separately_analytic_not_continuousAt :
    (∀ y : ℝ, AnalyticOnNhd ℝ (fun x : ℝ => x * y / (x ^ 2 + y ^ 2)) univ) ∧
    (∀ x : ℝ, AnalyticOnNhd ℝ (fun y : ℝ => x * y / (x ^ 2 + y ^ 2)) univ) ∧
    ¬ ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) (0, 0) :=
  spec_separately_analytic_not_continuousAt_aux

example : ¬ AnalyticAt ℝ (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) (0, 0) :=
  fun h => spec_separately_analytic_not_continuousAt.2.2 h.continuousAt

end HodgeLean.Foundations.AnalyticDivisorAlgebraic2
