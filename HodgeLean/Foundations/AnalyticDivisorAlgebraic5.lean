import HodgeLean.Foundations.AnalyticDivisorAlgebraic5Proofs

/-! # Germs and reduced equations: frozen specification (Chow/GAGA, fifth stage)

Toward `LefschetzOneOneHyp` for abelian `X` through the Appell--Humbert line bundle `L(H, χ)`:
(a) the line bundle with theta-function sections, (b) the analytic divisor of a section,
(c) Chow/GAGA, (d) the cycle class of that divisor is `c₁`. The fourth stage
(`HodgeLean.Foundations.AnalyticDivisorAlgebraic4`) proved convergent Weierstrass preparation and
division, and recommended this stage (b5): germs and reduced equations.

Coordinates are `ℂⁿ × ℂ = (Fin n → ℂ) × ℂ`, `(z, w)`, with sup norms. `monicInLast a` is
`(z, w) ↦ w ^ d + ∑_{j < d} a_j(z) w ^ j` (fourth stage); `monicPoly a z ∈ ℂ[X]` is the same
polynomial at a fixed `z`, `weierstrassDiscr a z` its discriminant (Mathlib's `Polynomial.discr`),
and `IsSquareFreeAt f y` says that `f` has no factorization `g ^ 2 * h` near `y` with `g`, `h`
analytic at `y` and `g y = 0` (`HodgeLean.Foundations.AnalyticDivisorAlgebraic5Defs`).

Claimed:
* **uniqueness of the Weierstrass preparation**: if `u · P = u' · P'` near `0` for monic
  polynomials `P`, `P'` of the same degree `d` in `w`, `u` a unit, `u'` analytic, and `P'` a
  Weierstrass polynomial, then `u = u'` and the coefficients agree near `0`; falsification: with
  `P' = w - 1` (a unit near `0`, not Weierstrass) and `P = w` it fails;
* **the multiplicity at a point**: for `f` analytic at `x` and not locally zero there, there is
  `m` with the order of `f` along every line through `x` at least `m`, and equal to `m` on a dense
  open set of directions; falsification: for `f = 0` no order is attained densely;
* **reduction to a germ regular in `w`**: such an `f` at `0`, composed with a suitable linear
  automorphism of `ℂⁿ × ℂ`, has a Weierstrass preparation of degree the multiplicity;
* **the discriminant**: `weierstrassDiscr a` is analytic where the `a j` are, and it is nonzero
  at `z` exactly when every root of `w ↦ monicInLast a (z, w)` is simple; the number of distinct
  roots is lower semicontinuous in `z`; where it is locally constant, `monicInLast a` is locally
  `∏ (w - φ_i(z)) ^ {m_i}` with analytic, pairwise distinct `φ_i`; off the discriminant locus the
  hypersurface is locally the union of `d` disjoint analytic graphs; falsification: at `z = 0`,
  `w ^ 2 - z₁` has no analytic root functions;
* **reduced equations**: if `monicInLast a` is a Weierstrass polynomial square-free at every point
  near `0`, its discriminant is not locally zero at `0`; falsifications: `(w - 1) ^ 2` (square-free
  near `0`, not Weierstrass) and `w ^ 2` (Weierstrass, not square-free) have discriminant `0`;
* **density of regular points**: for a Weierstrass-type polynomial with discriminant not locally
  zero, and for any `f` analytic at `0` and square-free at every point near `0`, every zero near
  `0` is a limit of regular zeros; falsification: for `w ^ 2` there are no regular zeros.

Not claimed: square-freeness at a point implying square-freeness at nearby points (coherence of
the reduced structure, Oka--Cartan), so the statements assume square-freeness on a neighbourhood;
the ring of germs being Noetherian or a UFD; irreducible germs or global irreducible components;
the Riemann extension theorem; multiplicities along components of a non-reduced divisor; closed
analyticity of the theta divisor in `X(ℂ)`; Chow's theorem or GAGA; algebraicity of any divisor;
or any cycle class. The route and stage estimates are in `docs/specs/AnalyticDivisorAlgebraic5.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Metric Polynomial

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic5

open HodgeLean.Foundations.AnalyticDivisorAlgebraic4

section Uniqueness

variable {n : ℕ}

/-- **Uniqueness of the Weierstrass preparation.**  Let `u` be analytic at `0` with `u 0 ≠ 0`,
`u'` analytic at `0`, and `P' = w ^ d + ∑_{j < d} a'_j(z) w ^ j` with every `a' j` continuous at
`0` and `a' j 0 = 0`. If `u · (w ^ d + ∑_{j < d} a_j(z) w ^ j) = u' · P'` near `0`, then `u = u'`
near `0` and `a j = a' j` near `0` for every `j`: with `q = u' / u - 1`, analytic at `0`, the
identity reads `q · P' + ∑_{j < d} (a'_j - a_j)(z) w ^ j = 0`, and Weierstrass division by `P'` is
unique.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Theorem 2
(uniqueness in the preparation theorem); Hörmander, *An Introduction to Complex Analysis in
Several Variables*, Theorem 6.1.1; with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_weierstrass_division_unique`. -/
theorem spec_weierstrass_preparation_unique {d : ℕ} {u u' : (Fin n → ℂ) × ℂ → ℂ}
    {a a' : Fin d → (Fin n → ℂ) → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hu' : AnalyticAt ℂ u' 0) (ha' : ∀ j, ContinuousAt (a' j) 0) (ha'0 : ∀ j, a' j 0 = 0)
    (h : (fun p => u p * monicInLast a p) =ᶠ[𝓝 0] fun p => u' p * monicInLast a' p) :
    u =ᶠ[𝓝 0] u' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j :=
  spec_weierstrass_preparation_unique_aux hu hu0 hu' ha' ha'0 h

example {d : ℕ} {u u' : (Fin n → ℂ) × ℂ → ℂ} {a a' : Fin d → (Fin n → ℂ) → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hu' : AnalyticAt ℂ u' 0)
    (ha' : ∀ j, ContinuousAt (a' j) 0) (ha'0 : ∀ j, a' j 0 = 0)
    (h : (fun p => u p * monicInLast a p) =ᶠ[𝓝 0] fun p => u' p * monicInLast a' p) :
    u 0 = u' 0 ∧ ∀ j, a j 0 = 0 := by
  obtain ⟨h1, h2⟩ := spec_weierstrass_preparation_unique hu hu0 hu' ha' ha'0 h
  exact ⟨h1.self_of_nhds, fun j => (h2 j).self_of_nhds.trans (ha'0 j)⟩

/-- **Falsification: uniqueness needs `P'` to be a Weierstrass polynomial.**  On `ℂ¹ × ℂ`,
`1 · w = (w / (w - 1)) · (w - 1)` near `0`, with `1` a unit, `w / (w - 1)` analytic at `0`, and
both factors monic of degree `1` in `w`; but `1 ≠ w / (w - 1)` near `0` (the coefficient
`a'_0 = -1` of `w - 1` does not vanish at `0`).

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B
(Definition 2, the coefficients of a Weierstrass polynomial vanish at the origin); elementary. -/
theorem spec_not_preparation_unique_of_unit :
    ((fun p : (Fin 1 → ℂ) × ℂ =>
        (1 : ℂ) * monicInLast (fun _ _ => (0 : ℂ) : Fin 1 → (Fin 1 → ℂ) → ℂ) p) =ᶠ[𝓝 0]
      fun p => p.2 / (p.2 - 1) *
        monicInLast (fun _ _ => (-1 : ℂ) : Fin 1 → (Fin 1 → ℂ) → ℂ) p) ∧
    ¬ ((fun _ => (1 : ℂ)) =ᶠ[𝓝 (0 : (Fin 1 → ℂ) × ℂ)] fun p => p.2 / (p.2 - 1)) :=
  spec_not_preparation_unique_of_unit_aux

example : ¬ ∀ (u u' : (Fin 1 → ℂ) × ℂ → ℂ) (a a' : Fin 1 → (Fin 1 → ℂ) → ℂ),
    AnalyticAt ℂ u 0 → u 0 ≠ 0 → AnalyticAt ℂ u' 0 → (∀ j, ContinuousAt (a' j) 0) →
    ((fun p => u p * monicInLast a p) =ᶠ[𝓝 0] fun p => u' p * monicInLast a' p) →
    u =ᶠ[𝓝 0] u' := fun H =>
  spec_not_preparation_unique_of_unit.2
    (H _ _ _ _ analyticAt_const one_ne_zero
      (analyticAt_snd.div (analyticAt_snd.sub analyticAt_const) (by simp))
      (fun _ => continuousAt_const) spec_not_preparation_unique_of_unit.1)

end Uniqueness

section Multiplicity

/-- **The multiplicity of a hypersurface at a point.**  Let `f : E → ℂ` be analytic at `x` and
not identically zero near `x`. There is `m : ℕ` such that `f` vanishes to order at least `m` along
every line `t ↦ x + t • v` at `t = 0`, and to order exactly `m` for `v` in a dense open set: with
`f (x + y) = ∑_k P_k(y)` the expansion in homogeneous polynomials, `m` is the least `k` with
`P_k ≠ 0`, the order along `v` is the least `k` with `P_k(v) ≠ 0`, and `{P_m ≠ 0}` is open and
dense.

Source: Chirka, *Complex Analytic Sets*, §2.1 (multiplicity of a hypersurface at a point, the
order along a generic line); Gunning--Rossi, *Analytic Functions of Several Complex Variables*,
Ch. II, §B, Lemma 1 (general position); Mathlib's `HasFPowerSeriesAt` and
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
theorem spec_exists_multiplicity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (hf0 : ¬ ∀ᶠ y in 𝓝 x, f y = 0) :
    ∃ m : ℕ, (∀ v : E, (m : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x + t • v)) 0) ∧
      IsOpen {v : E | analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = m} ∧
      Dense {v : E | analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = m} :=
  spec_exists_multiplicity_aux hf hf0

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hf0 : ¬ ∀ᶠ y in 𝓝 x, f y = 0) :
    ∃ v : E, analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 ≠ ⊤ := by
  obtain ⟨m, -, -, hd⟩ := spec_exists_multiplicity hf hf0
  obtain ⟨v, hv⟩ := hd.nonempty
  exact ⟨v, by rw [show _ = _ from hv]; exact ENat.natCast_ne_top m⟩

variable {n : ℕ}

/-- **Falsification: the multiplicity needs `f` not locally zero.**  For `f = 0` on `ℂⁿ × ℂ`,
the order along every line is `⊤`, so no natural number is attained on a dense set of
directions.

Source: Chirka, *Complex Analytic Sets*, §2.1 (the multiplicity is defined for `f ≢ 0`);
Mathlib's `analyticOrderAt_eq_top`. -/
theorem spec_not_exists_dense_order_zero :
    ¬ ∃ m : ℕ, Dense {v : (Fin n → ℂ) × ℂ |
      analyticOrderAt (fun t : ℂ => (fun _ : (Fin n → ℂ) × ℂ => (0 : ℂ)) (0 + t • v)) 0 = m} :=
  spec_not_exists_dense_order_zero_aux

example : ¬ ∀ f : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ f 0 →
    ∃ m : ℕ, Dense {v : (Fin n → ℂ) × ℂ | analyticOrderAt (fun t : ℂ => f (0 + t • v)) 0 = m} :=
  fun H => spec_not_exists_dense_order_zero (H _ analyticAt_const)

/-- **Preparation in generic linear coordinates.**  Let `f : ℂⁿ × ℂ → ℂ` be analytic at `0` and
not identically zero near `0`, of multiplicity `m` at `0`. There is a linear automorphism `L` of
`ℂⁿ × ℂ` such that `f ∘ L = u · (w ^ m + ∑_{j < m} a_j(z) w ^ j)` near `0`, with `u` analytic at
`0`, `u 0 ≠ 0`, and every `a j` analytic at `0` with `a j 0 = 0`: any `L` sending `(0, 1)` into
the dense open set of directions of order `m` makes `w ↦ f (L (0, w))` of order `m`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, Lemma 1
(after a linear change of coordinates `f (0, w) ≢ 0`) and Theorem 2; Mathlib's
`SeparatingDual.exists_continuousLinearEquiv_apply_eq`; with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_weierstrass_preparation`. -/
theorem spec_exists_linearEquiv_preparation {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : ¬ ∀ᶠ p in 𝓝 0, f p = 0) :
    ∃ m : ℕ, (∀ v, (m : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (t • v)) 0) ∧
      ∃ L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ),
        ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
          ∃ a : Fin m → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
            (fun p => f (L p)) =ᶠ[𝓝 0] fun p => u p * monicInLast a p :=
  spec_exists_linearEquiv_preparation_aux hf hf0

example {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : ¬ ∀ᶠ p in 𝓝 0, f p = 0) :
    ∃ L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ), ∃ m : ℕ,
      analyticOrderAt (fun w => f (L (0, w))) 0 = m := by
  obtain ⟨m, -, L, u, hu, hu0, a, ha, h⟩ := spec_exists_linearEquiv_preparation hf hf0
  exact ⟨L, m, spec_analyticOrderAt_of_preparation hu hu0 (fun j => (ha j).2) h⟩

end Multiplicity

section Discriminant

variable {n : ℕ}

/-- **The polynomial at a fixed `z`.**  `monicPoly a z` is monic of degree `d`, and evaluating it
at `w` gives `monicInLast a (z, w)`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B,
Definition 2; Mathlib's `Polynomial.Monic` and `Polynomial.eval`. -/
theorem spec_monicPoly {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (monicPoly a z).Monic ∧ (monicPoly a z).natDegree = d ∧
      ∀ w, (monicPoly a z).eval w = monicInLast a (z, w) :=
  spec_monicPoly_aux a z

example {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : monicPoly a z ≠ 0 :=
  (spec_monicPoly a z).1.ne_zero

/-- **The discriminant is analytic.**  If every coefficient `a j` is analytic at `z₀`, so is
`z ↦ weierstrassDiscr a z`: the discriminant of a monic polynomial of fixed degree `d` is a
polynomial with integer coefficients in its coefficients.

Source: Lang, *Algebra*, rev. 3rd ed., Ch. IV, §6 (the discriminant as a polynomial in the
coefficients); Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A;
Mathlib's `Polynomial.discr` and `Polynomial.sylvesterDeriv`. -/
theorem spec_analyticAt_weierstrassDiscr {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z₀ : Fin n → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z₀) :
    AnalyticAt ℂ (weierstrassDiscr a) z₀ :=
  spec_analyticAt_weierstrassDiscr_aux ha

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₀) : ContinuousAt (weierstrassDiscr a) z₀ :=
  (spec_analyticAt_weierstrassDiscr ha).continuousAt

/-- **The discriminant detects multiple roots.**  `weierstrassDiscr a z ≠ 0` if and only if
`w ↦ monicInLast a (z, w)` vanishes to order at most `1` at every point, i.e. all its roots are
simple: over `ℂ`, the discriminant of a monic polynomial is nonzero iff the polynomial is
separable (`resultant_deriv`, `resultant_eq_zero_iff`), and the analytic order of a polynomial
function is the root multiplicity.

Source: Lang, *Algebra*, rev. 3rd ed., Ch. IV, §6 and Ch. V, §6 (separable polynomials);
Mathlib's `Polynomial.resultant_deriv`, `Polynomial.resultant_eq_zero_iff`,
`Polynomial.nodup_roots_iff_of_splits`; with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_analyticOrderAt_polynomial_eval`. -/
theorem spec_weierstrassDiscr_ne_zero_iff {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    weierstrassDiscr a z ≠ 0 ↔ ∀ w, analyticOrderAt (fun w => monicInLast a (z, w)) w ≤ 1 :=
  spec_weierstrassDiscr_ne_zero_iff_aux a z

example {d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (h : ∃ w, 2 ≤ analyticOrderAt (fun w => monicInLast a (z, w)) w) :
    weierstrassDiscr a z = 0 := by
  by_contra hD
  obtain ⟨w, hw⟩ := h
  have := (spec_weierstrassDiscr_ne_zero_iff a z).1 hD w
  exact absurd (hw.trans this) (by decide)

/-- **The number of distinct roots is lower semicontinuous.**  If every `a j` is analytic at
`z₁`, then for `z` near `z₁` the polynomial `monicPoly a z` has at least as many distinct roots as
`monicPoly a z₁`: each root of `w ↦ monicInLast a (z₁, w)` persists in a small disc around it.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B, proof of
Theorem 2 (root counting in families); Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §5.2
(Hurwitz's theorem); with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_zeroCount_eq_order`. -/
theorem spec_eventually_card_roots_le {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z₁ : Fin n → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z₁) :
    ∀ᶠ z in 𝓝 z₁,
      (monicPoly a z₁).roots.toFinset.card ≤ (monicPoly a z).roots.toFinset.card :=
  spec_eventually_card_roots_le_aux ha

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₁ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₁) :
    ∃ z, (monicPoly a z₁).roots.toFinset.card ≤ (monicPoly a z).roots.toFinset.card :=
  (spec_eventually_card_roots_le ha).exists

/-- **Root graphs where the number of distinct roots is locally constant.**  Let every `a j` be
analytic at `z₁`, and let `monicPoly a z` have exactly `k` distinct roots for all `z` near `z₁`.
Then there are functions `φ_i`, `i < k`, analytic at `z₁`, and multiplicities `m_i ≥ 1` such that
near `z₁`, `monicInLast a (z, w) = ∏_i (w - φ_i(z)) ^ {m_i}` for all `w`, with the `φ_i(z)`
pairwise distinct: each disc around a root of `monicInLast a (z₁, ·)` contains exactly one distinct
root `φ_i(z)`, of constant multiplicity `m_i`, and
`φ_i(z) = (2πi m_i)⁻¹ ∮ w ∂_w P (z, w) / P (z, w) dw` is analytic.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A (local
structure of the zeros of a Weierstrass polynomial) and Ch. II, §B, proof of Theorem 2; with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_circleIntegral_mul_logDeriv` and
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_analyticOnNhd_circleIntegral`. -/
theorem spec_exists_root_graphs_pow {d k : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    {z₁ : Fin n → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z₁)
    (hk : ∀ᶠ z in 𝓝 z₁, (monicPoly a z).roots.toFinset.card = k) :
    ∃ φ : Fin k → (Fin n → ℂ) → ℂ, ∃ m : Fin k → ℕ, (∀ i, AnalyticAt ℂ (φ i) z₁ ∧ 1 ≤ m i) ∧
      ∀ᶠ z in 𝓝 z₁, (∀ w, monicInLast a (z, w) = ∏ i, (w - φ i z) ^ m i) ∧
        Pairwise fun i j => φ i z ≠ φ j z :=
  spec_exists_root_graphs_pow_aux ha hk

example {d k : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₁ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₁)
    (hk : ∀ᶠ z in 𝓝 z₁, (monicPoly a z).roots.toFinset.card = k) :
    ∃ φ : Fin k → (Fin n → ℂ) → ℂ, ∀ᶠ z in 𝓝 z₁, ∀ i, monicInLast a (z, φ i z) = 0 := by
  obtain ⟨φ, m, hφ, h⟩ := spec_exists_root_graphs_pow ha hk
  refine ⟨φ, h.mono fun z hz i => ?_⟩
  rw [hz.1]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by rw [sub_self]; exact zero_pow (Nat.one_le_iff_ne_zero.1 (hφ i).2))

/-- **Off the discriminant locus the hypersurface is `d` disjoint analytic graphs.**  Let every
`a j` be analytic at `z₀`, with `weierstrassDiscr a z₀ ≠ 0`. Then there are `d` functions `φ_i`
analytic at `z₀` such that near `z₀`, `monicInLast a (z, w) = ∏_i (w - φ_i(z))` for all `w`, with
the `φ_i(z)` pairwise distinct: over a neighbourhood of `z₀` the zero set of `monicInLast a` is the
union of the `d` disjoint graphs `w = φ_i(z)`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A (outside
the discriminant locus a Weierstrass polynomial splits into `d` holomorphic linear factors);
Chirka, *Complex Analytic Sets*, §1.3 (analytic covers). -/
theorem spec_exists_root_graphs {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₀) (hD : weierstrassDiscr a z₀ ≠ 0) :
    ∃ φ : Fin d → (Fin n → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (φ i) z₀) ∧
      ∀ᶠ z in 𝓝 z₀, (∀ w, monicInLast a (z, w) = ∏ i, (w - φ i z)) ∧
        Pairwise fun i j => φ i z ≠ φ j z :=
  spec_exists_root_graphs_aux ha hD

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z₀) (hD : weierstrassDiscr a z₀ ≠ 0) :
    ∃ φ : Fin d → (Fin n → ℂ) → ℂ, ∀ᶠ z in 𝓝 z₀, ∀ i, monicInLast a (z, φ i z) = 0 := by
  obtain ⟨φ, -, h⟩ := spec_exists_root_graphs ha hD
  exact ⟨φ, h.mono fun z hz i => by
    rw [hz.1]; exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)⟩

/-- **Falsification: on the discriminant locus there are no analytic root graphs.**  For
`P (z, w) = w ^ 2 - z₁` on `ℂ¹ × ℂ` the discriminant vanishes at `z = 0`, and there are no
functions `φ₀`, `φ₁` analytic at `0` with `P (z, w) = (w - φ₀(z)) (w - φ₁(z))` near `0`: they would
give `φ₀(z) ^ 2 = z₁`, and the order of `t ↦ φ₀(t) ^ 2` at `0` is even.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A (branching
over the discriminant locus); Ahlfors, *Complex Analysis*, 3rd ed., Ch. 8, §1 (no analytic square
root of `z` at `0`). -/
theorem spec_not_exists_root_graphs_sq_sub :
    weierstrassDiscr (![fun z => -z 0, fun _ => 0] : Fin 2 → (Fin 1 → ℂ) → ℂ) 0 = 0 ∧
    ¬ ∃ φ : Fin 2 → (Fin 1 → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (φ i) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ w,
        monicInLast (![fun z => -z 0, fun _ => 0] : Fin 2 → (Fin 1 → ℂ) → ℂ) (z, w) =
          ∏ i, (w - φ i z) :=
  spec_not_exists_root_graphs_sq_sub_aux

example : ¬ ∀ a : Fin 2 → (Fin 1 → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0) →
    ∃ φ : Fin 2 → (Fin 1 → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (φ i) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ w, monicInLast a (z, w) = ∏ i, (w - φ i z) := by
  intro H
  refine spec_not_exists_root_graphs_sq_sub.2 (H _ fun j => ?_)
  fin_cases j
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0).neg
  · exact analyticAt_const

end Discriminant

section Reduced

variable {n : ℕ}

/-- **A reduced Weierstrass polynomial has a discriminant not identically zero.**  Let every `a j`
be analytic at `0` with `a j 0 = 0`, and let `monicInLast a` be square-free at every point near
`0`. Then `weierstrassDiscr a` is not identically zero near `0`. Otherwise every
`monicInLast a (z, ·)` near `0` has a multiple root; at a point `z₁` near `0` where the number of
distinct roots is locally maximal, `spec_exists_root_graphs_pow` gives a factor
`(w - φ_i(z)) ^ {m_i}` with `m_i ≥ 2`, contradicting square-freeness at `(z₁, φ_i(z₁))`, which is
near `0` because the roots of a Weierstrass polynomial are small.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A (the
discriminant of a reduced Weierstrass polynomial is not identically zero); Chirka, *Complex
Analytic Sets*, §2.3; with
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small`. -/
theorem spec_weierstrassDiscr_not_eventually_zero {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) (ha0 : ∀ j, a j 0 = 0)
    (hsq : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), IsSquareFreeAt (monicInLast a) y) :
    ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0 :=
  spec_weierstrassDiscr_not_eventually_zero_aux ha ha0 hsq

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (ha0 : ∀ j, a j 0 = 0)
    (hsq : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), IsSquareFreeAt (monicInLast a) y) :
    ∃ᶠ z in 𝓝 0, weierstrassDiscr a z ≠ 0 :=
  Filter.not_eventually.1 (spec_weierstrassDiscr_not_eventually_zero ha ha0 hsq)

/-- **Falsification: the coefficients must vanish at `0`.**  On `ℂ¹ × ℂ`,
`P (z, w) = w ^ 2 - 2 w + 1 = (w - 1) ^ 2` has no zero near `0`, so it is square-free at every point
near `0`, yet its discriminant vanishes identically: the repeated root `1` lies away from `0`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B
(Definition 2); Mathlib's `Polynomial.discr_of_degree_eq_two`. -/
theorem spec_weierstrassDiscr_sub_one_sq :
    (∀ᶠ y in 𝓝 (0 : (Fin 1 → ℂ) × ℂ),
      IsSquareFreeAt (monicInLast (![fun _ => 1, fun _ => -2] : Fin 2 → (Fin 1 → ℂ) → ℂ)) y) ∧
    ∀ z, weierstrassDiscr (![fun _ => 1, fun _ => -2] : Fin 2 → (Fin 1 → ℂ) → ℂ) z = 0 :=
  spec_weierstrassDiscr_sub_one_sq_aux

example : ¬ ∀ a : Fin 2 → (Fin 1 → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0) →
    (∀ᶠ y in 𝓝 (0 : (Fin 1 → ℂ) × ℂ), IsSquareFreeAt (monicInLast a) y) →
    ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0 := by
  intro H
  refine H _ (fun j => ?_) spec_weierstrassDiscr_sub_one_sq.1
    (Eventually.of_forall spec_weierstrassDiscr_sub_one_sq.2)
  fin_cases j <;> exact analyticAt_const

/-- **Falsification: square-freeness is needed.**  On `ℂ¹ × ℂ`, the Weierstrass polynomial
`P (z, w) = w ^ 2` is not square-free at `0` (`P = w ^ 2 · 1`) and its discriminant vanishes
identically.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A;
Mathlib's `Polynomial.discr_of_degree_eq_two`. -/
theorem spec_weierstrassDiscr_sq :
    ¬ IsSquareFreeAt (monicInLast (fun _ _ => 0 : Fin 2 → (Fin 1 → ℂ) → ℂ)) 0 ∧
    ∀ z, weierstrassDiscr (fun _ _ => 0 : Fin 2 → (Fin 1 → ℂ) → ℂ) z = 0 :=
  spec_weierstrassDiscr_sq_aux

example : ¬ ∀ a : Fin 2 → (Fin 1 → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) 0) → (∀ j, a j 0 = 0) →
    ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0 := fun H =>
  H _ (fun _ => analyticAt_const) (fun _ => rfl)
    (Eventually.of_forall spec_weierstrassDiscr_sq.2)

end Reduced

section Regular

variable {n : ℕ}

/-- **Density of regular points for a polynomial with nonzero discriminant.**  Let every `a j`
be analytic at `0`, with `weierstrassDiscr a` not identically zero near `0`. Then every zero `y`
of `monicInLast a` near `0` is a limit of zeros `p` with `∂_w monicInLast a (p) ≠ 0` (in particular
regular points of the hypersurface): the discriminant is nonzero on a dense subset of a ball, over
which the roots are simple, and roots depend continuously on `z`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A (the
regular points of a reduced hypersurface are dense); Chirka, *Complex Analytic Sets*, §2.3; with
`spec_weierstrassDiscr_ne_zero_iff` and
`HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_zeroCount_eq_order`. -/
theorem spec_eventually_mem_closure_regular_monicInLast {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (hD : ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0) :
    ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), monicInLast a y = 0 →
      y ∈ closure {p | monicInLast a p = 0 ∧ deriv (fun w => monicInLast a (p.1, w)) p.2 ≠ 0} :=
  spec_eventually_mem_closure_regular_monicInLast_aux ha hD

example {d : ℕ} {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (hD : ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0) (h0 : monicInLast a 0 = 0) :
    (0 : (Fin n → ℂ) × ℂ) ∈
      closure {p | monicInLast a p = 0 ∧ deriv (fun w => monicInLast a (p.1, w)) p.2 ≠ 0} :=
  (spec_eventually_mem_closure_regular_monicInLast ha hD).self_of_nhds h0

/-- **Density of regular points of a reduced hypersurface.**  Let `f : ℂⁿ × ℂ → ℂ` be analytic at
`0` and square-free at every point near `0`. Then every zero of `f` near `0` is a limit of regular
zeros, points `p` with `f p = 0` and `df(p) ≠ 0`: after a linear change of coordinates `f` is a
unit times a Weierstrass polynomial, square-free near `0`, whose discriminant is therefore not
identically zero.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A;
Chirka, *Complex Analytic Sets*, §2.3 (the regular points of a hypersurface with reduced equation
are dense in it); with `spec_exists_linearEquiv_preparation`,
`spec_weierstrassDiscr_not_eventually_zero` and
`spec_eventually_mem_closure_regular_monicInLast`. -/
theorem spec_eventually_mem_closure_regular {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hsq : ∀ᶠ y in 𝓝 0, IsSquareFreeAt f y) :
    ∀ᶠ y in 𝓝 0, f y = 0 → y ∈ closure {p | f p = 0 ∧ fderiv ℂ f p ≠ 0} :=
  spec_eventually_mem_closure_regular_aux hf hsq

example {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hsq : ∀ᶠ y in 𝓝 0, IsSquareFreeAt f y) (h0 : f 0 = 0) :
    (0 : (Fin n → ℂ) × ℂ) ∈ closure {p | f p = 0 ∧ fderiv ℂ f p ≠ 0} :=
  (spec_eventually_mem_closure_regular hf hsq).self_of_nhds h0

/-- **Falsification: density of regular points needs a reduced equation.**  For
`f (z, w) = w ^ 2` on `ℂⁿ × ℂ`, the zero set is `{w = 0}` but `df = 2 w dw` vanishes on it, so
there are no regular zeros and `0` is not in the closure of the regular zeros.

Source: Chirka, *Complex Analytic Sets*, §2.3 (the equation of a hypersurface must be reduced);
elementary. -/
theorem spec_not_mem_closure_regular_sq :
    (0 : (Fin n → ℂ) × ℂ) ∉
      closure {p | p.2 ^ 2 = 0 ∧ fderiv ℂ (fun q : (Fin n → ℂ) × ℂ => q.2 ^ 2) p ≠ 0} :=
  spec_not_mem_closure_regular_sq_aux

example : ¬ ∀ f : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ f 0 → f 0 = 0 →
    (0 : (Fin n → ℂ) × ℂ) ∈ closure {p | f p = 0 ∧ fderiv ℂ f p ≠ 0} := fun H =>
  spec_not_mem_closure_regular_sq (H (fun q => q.2 ^ 2) (analyticAt_snd.pow 2) (by simp))

end Regular

end HodgeLean.Foundations.AnalyticDivisorAlgebraic5
