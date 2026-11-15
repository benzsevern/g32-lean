import HodgeLean.Papers.G34SupplyProofs

/-! # G34 Theorem A, stage 3: the Brauer/Schoen supply (FROZEN SPEC)

Stage 3 of the premise-first route to G34 v1.5 Theorem A, at `(n, δ) = (4, [1])` of the generic
Weil transfer: the finite inputs of the supplier argument (G34 Section 4, Theorem 5.1, Example 9.3)
that the repository can state and check, the direct named premise `g34s_Prop46` for the output of
Proposition 4.6 and Corollary 4.7, and the bridge `g34s_fiber_alg` into the stage field
`fiber_alg`.

Claimed:
* the ten skeleton generators `s_i` are involutions in `skelg34_group`, the printed tuple
  `(s₁, s₁, …, s₁₀, s₁₀)` has product one, and every entry of it is conjugate to its inverse
  (the branch classes are real);
* if `skelg34_group` is finite, every supplier `(H′, χ)` of order `m ≥ 3` on the printed tuple
  with `h = 2q - 2 + s > 0` is admissible (`h` even, exponents simple), with `q` the
  Riemann–Hurwitz genus `skelg34_genus`; this is the G34 instance of the admissibility step of
  Theorem 5.1;
* for a finite group over a field `k` with `IsAlgClosed k` and `CharZero k`: `𝖺(σ) = e_σ` on
  the free coordinates, and a Brauer decomposition of `σ` (an explicit binder, Brauer's theorem is
  not proved) gives `e_σ` as the integer combination of the `a(λ_i)` over the terms of order at
  least three, the terms of order one or two vanishing;
* the arithmetic of Example 9.3 (`|H′| = 2 · 3⁷ = 4374`, `q = 35 841`, `h = 71 680`,
  admissible) and of Lemma 4.4's trigger (if `4 ∣ m`, every prime divisor of `m` divides `m/2`);
* the implication from the named premise `g34s_Prop46` to the stage field `fiber_alg`.

Not claimed: Schoen's theorem, Lemma 4.4, Milne's theorem or the contraction of Proposition 4.6
(the Jacobian factors, products, Künneth, correspondences and pushforward are absent); the
existence of a Brauer decomposition; the finiteness or order of `skelg34_group`; the 84-row
identity of Remark 9.2. Proposition 4.6 and Corollary 4.7 enter as the one premise
`g34s_Prop46`, so Lean checks the finite inputs and not the supplier argument. Theorem A remains
unasserted.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory

namespace HodgeLean.Papers

/-! ## The printed tuple -/

/-- **Each skeleton generator is an involution**: `s_i * s_i = 1` in `skelg34_group`.
Source: G34 v1.5, Section 9 ("Its product is `1` because every `s_i` is an involution") and
Appendix A. -/
theorem g34s_generator_sq (i : Fin 10) :
    skelg34_generator i * skelg34_generator i = 1 :=
  g34s_generator_sq_aux i

example (i : Fin 10) : (skelg34_generator i)⁻¹ = skelg34_generator i :=
  inv_eq_of_mul_eq_one_right (g34s_generator_sq i)

/-- **The printed tuple has product one** in `skelg34_group`.
Source: G34 v1.5, Section 9 ("Its product is `1` because every `s_i` is an involution"). -/
theorem g34s_tuple_prod : skelg34_tuple.prod = 1 :=
  g34s_tuple_prod_aux

example : skelg34_tuple.length = 20 ∧ skelg34_tuple.prod = 1 :=
  ⟨by decide, g34s_tuple_prod⟩

/-- **The branch classes are real**: every entry of the printed tuple is conjugate in
`skelg34_group` to its inverse.
Source: G34 v1.5, proof of Theorem A ("The reflections of `G₃₄` are involutions, so the branch
classes are real") and Section 5 ("involutions are real"). -/
theorem g34s_tuple_real :
    ∀ g ∈ skelg34_tuple, ∃ w : skelg34_group, w * g * w⁻¹ = g⁻¹ :=
  g34s_tuple_real_aux

example : ∃ w : skelg34_group, w * skelg34_generator 0 * w⁻¹ = (skelg34_generator 0)⁻¹ :=
  g34s_tuple_real _ (by simp [skelg34_tuple])

/-! ## Admissibility of the suppliers -/

/-- **Every supplier on the printed tuple with `h > 0` is admissible.** For a finite
`skelg34_group` and a supplier `(H′, χ)` of order `m ≥ 3` (`skelg34_Supplier`), with `q` the
Riemann–Hurwitz genus of `C/H′` and `s` the number of branch exponents, `h = 2q - 2 + s > 0`
implies that `h` is even and the exponents are simple.
Source: G34 v1.5, Theorem 5.1 (`thm:brauer`), proof ("These suppliers are admissible"), applied to
the printed tuple of Section 9; Definition 4.1 and the following paragraph (admissibility);
through `papers_g34_exps_tuple_admissible`. -/
theorem g34s_supplier_admissible [Finite skelg34_group] (S : skelg34_Supplier)
    (hh : 0 < (2 * skelg34_genus S.H skelg34_tuple - 2 +
      (papersExpsList S.H S.eps skelg34_tuple).length : ℤ)) :
    SupplierAdmissible S.m (skelg34_genus S.H skelg34_tuple)
      (papersExpsList S.H S.eps skelg34_tuple) :=
  g34s_supplier_admissible_aux S hh

example [Finite skelg34_group] (S : skelg34_Supplier)
    (hh : 0 < (2 * skelg34_genus S.H skelg34_tuple - 2 +
      (papersExpsList S.H S.eps skelg34_tuple).length : ℤ)) :
    IsSimpleExps S.m (papersExpsList S.H S.eps skelg34_tuple) :=
  (g34s_supplier_admissible S hh).2.2

/-! ## The Brauer character identity -/

/-- **`𝖺(σ) = e_σ` on the free coordinates.** If `σ` is simple, isomorphic to `τ i₀` and to no
other `τ i`, and to no `τ̄ i`, with all `τ i`, `τ̄ i` simple, then the free coordinates of the
class-function map `𝖺` at the character of `σ` are `Pi.single i₀ 1`.
Source: G34 v1.5, Theorem 5.1 (`thm:brauer`), proof ("It is additive, `𝖺(σ) = e_σ`"), and
Subsection 4.2 (`e_σ`: coordinate `+1` at the pair of `σ`); Serre, *Linear Representations of
Finite Groups*, §2.3, Theorem 3 (Mathlib's `FDRep.char_orthonormal`). -/
theorem g34s_a_sigma {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {G : Type*}
    [Group G] [Fintype G] {ι κ : Type*} [DecidableEq ι] (τ τbar : ι → FDRep k G)
    (η : κ → FDRep k G) (σ : FDRep k G) (i₀ : ι) (hσ : Simple σ) (hτ : ∀ i, Simple (τ i))
    (hτbar : ∀ i, Simple (τbar i)) (hστ : ∀ i, Nonempty (σ ≅ τ i) ↔ i = i₀)
    (hστbar : ∀ i, IsEmpty (σ ≅ τbar i)) :
    (papersACF τ τbar η σ.character).1 = Pi.single i₀ 1 :=
  g34s_a_sigma_aux τ τbar η σ i₀ hσ hτ hτbar hστ hστbar

example {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {G : Type*} [Group G] [Fintype G]
    {ι κ : Type*} [DecidableEq ι] (τ τbar : ι → FDRep k G) (η : κ → FDRep k G)
    (σ : FDRep k G) (i₀ : ι) (hσ : Simple σ) (hτ : ∀ i, Simple (τ i))
    (hτbar : ∀ i, Simple (τbar i)) (hστ : ∀ i, Nonempty (σ ≅ τ i) ↔ i = i₀)
    (hστbar : ∀ i, IsEmpty (σ ≅ τbar i)) :
    (papersACF τ τbar η σ.character).1 i₀ = 1 := by
  rw [g34s_a_sigma τ τbar η σ i₀ hσ hτ hτbar hστ hστbar, Pi.single_eq_same]

open Classical in
/-- **A Brauer decomposition, with the real terms removed.** If the character of `σ` is
`∑ n_i Ind_{B_i}^G λ_i` (Brauer's theorem, an explicit binder), then the free coordinates of
`𝖺(σ)` are `∑ n_i a(λ_i)` over the terms with `λ_i² ≠ 1`: the terms of order one or two vanish.
Source: G34 v1.5, Theorem 5.1 (`thm:brauer`), proof ("Brauer induction" and "Terms that
vanish"); through `papers_g34_a_brauer` and `papers_g34_order_two_free`. -/
theorem g34s_brauer_free {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G]
    [Fintype G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (σ : FDRep k G)
    (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) {N : ℕ}
    (Hs : Fin N → Subgroup G) [∀ i, Fintype (Hs i)] (lam : (i : Fin N) → Hs i →* kˣ)
    (n : Fin N → ℤ)
    (hbrauer : ∀ g, σ.character g =
      ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g) :
    (papersACF τ τbar η σ.character).1 =
      ∑ i ∈ Finset.univ.filter (fun i => lam i ^ 2 ≠ 1),
        (n i : k) • (fun i' => ((papersA τ τbar η (Hs i) (lam i)).1 i' : k)) :=
  g34s_brauer_free_aux τ τbar η σ hbar Hs lam n hbrauer

/-- With no Brauer terms, the free coordinates of `𝖺(σ)` vanish. -/
example {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] [Fintype G] {ι κ : Type*}
    (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (σ : FDRep k G)
    (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹)
    (hσ : ∀ g, σ.character g = 0) :
    (papersACF τ τbar η σ.character).1 = 0 := by
  classical
  have h := g34s_brauer_free τ τbar η σ hbar (N := 0) Fin.elim0 (fun i => Fin.elim0 i)
    Fin.elim0 (fun g => by simp [hσ g])
  simpa using h

open Classical in
/-- **The Brauer character identity for `e_σ`.** Under the hypotheses of `g34s_a_sigma` and
`g34s_brauer_free`, `e_σ = ∑ n_i a(λ_i)` on the free coordinates, the sum running over the terms
with `λ_i² ≠ 1`.
Source: G34 v1.5, Theorem 5.1 (`thm:brauer`), proof ("Hence `e_σ = ∑ n_i a(λ_i)`" and "Terms that
vanish"); Serre, *Linear Representations of Finite Groups*, §10.5, Theorem 20 (the decomposition,
here a binder). -/
theorem g34s_brauer_identity {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G] {ι κ : Type*} [DecidableEq ι] (τ τbar : ι → FDRep k G)
    (η : κ → FDRep k G) (σ : FDRep k G) (i₀ : ι) (hσ : Simple σ) (hτ : ∀ i, Simple (τ i))
    (hτbar : ∀ i, Simple (τbar i)) (hστ : ∀ i, Nonempty (σ ≅ τ i) ↔ i = i₀)
    (hστbar : ∀ i, IsEmpty (σ ≅ τbar i))
    (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) {N : ℕ}
    (Hs : Fin N → Subgroup G) [∀ i, Fintype (Hs i)] (lam : (i : Fin N) → Hs i →* kˣ)
    (n : Fin N → ℤ)
    (hbrauer : ∀ g, σ.character g =
      ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g) :
    (Pi.single i₀ 1 : ι → k) =
      ∑ i ∈ Finset.univ.filter (fun i => lam i ^ 2 ≠ 1),
        (n i : k) • (fun i' => ((papersA τ τbar η (Hs i) (lam i)).1 i' : k)) :=
  g34s_brauer_identity_aux τ τbar η σ i₀ hσ hτ hτbar hστ hστbar hbar Hs lam n hbrauer

/-- A decomposition with only real terms would make `e_σ` vanish; the identity forces a term of
order at least three. -/
example {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {G : Type*} [Group G] [Fintype G]
    {ι κ : Type*} [DecidableEq ι] (τ τbar : ι → FDRep k G) (η : κ → FDRep k G)
    (σ : FDRep k G) (i₀ : ι) (hσ : Simple σ) (hτ : ∀ i, Simple (τ i))
    (hτbar : ∀ i, Simple (τbar i)) (hστ : ∀ i, Nonempty (σ ≅ τ i) ↔ i = i₀)
    (hστbar : ∀ i, IsEmpty (σ ≅ τbar i))
    (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) {N : ℕ}
    (Hs : Fin N → Subgroup G) [∀ i, Fintype (Hs i)] (lam : (i : Fin N) → Hs i →* kˣ)
    (n : Fin N → ℤ)
    (hbrauer : ∀ g, σ.character g =
      ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g) :
    ∃ i, lam i ^ 2 ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  have h := g34s_brauer_identity τ τbar η σ i₀ hσ hτ hτbar hστ hστbar hbar Hs lam n hbrauer
  have hempty : Finset.univ.filter (fun i => lam i ^ 2 ≠ 1) = ∅ :=
    Finset.filter_false_of_mem (fun i _ => not_not.mpr (hno i))
  rw [hempty, Finset.sum_empty] at h
  have := congrFun h i₀
  simp at this

/-! ## Finite arithmetic of Example 9.3 and Lemma 4.4 -/

/-- **Example 9.3's arithmetic.** `|G₃₄| = 2⁹ · 3⁷ · 5 · 7`, so a Sylow `3`-subgroup has order
`3⁷` and `|⟨-I₆⟩ × P| = 2 · 3⁷ = 4374`; the unramified Riemann–Hurwitz relation
`8 |G₃₄| = 4374 (2q - 2)` holds at `q = 35 841`; `h = 2q - 2 = 71 680`; and with no branch
exponents the supplier is admissible for `m = 3`. The order enters as the printed number.
Source: G34 v1.5, Example 9.3 (`ex:supplier`) and Section 9 (`|G₃₄| = 39 191 040`). -/
theorem g34s_example_supplier :
    (39191040 : ℕ) = 2 ^ 9 * 3 ^ 7 * 5 * 7 ∧ (2 * 3 ^ 7 : ℕ) = 4374 ∧
      8 * (39191040 : ℤ) = 4374 * (2 * 35841 - 2) ∧ (2 * 35841 - 2 : ℤ) = 71680 ∧
      SupplierAdmissible 3 35841 [] :=
  g34s_example_supplier_aux

example : (2 * 35841 - 2 : ℤ) = 71680 := g34s_example_supplier.2.2.2.1

/-- **The trigger of Lemma 4.4.** If `4 ∣ m`, every prime `p ∣ m` divides `m/2`; so when every
exponent is `m/2`, no `ℤ/p`-quotient of the cyclic cover is ramified, and Schoen's choice of a
prime in Sublemma 2.9 is unavailable.
Source: G34 v1.5, Section 4, paragraph before Lemma 4.4 ("When every exponent equals `m/2` and
`4 ∣ m`, no such prime exists"); Schoen, Compositio Math. 65 (1988), Sublemma 2.9. -/
theorem g34s_half_exponent_no_prime (m p : ℕ) (hm : 4 ∣ m) (hp : p.Prime) (hpm : p ∣ m) :
    p ∣ m / 2 :=
  g34s_half_exponent_no_prime_aux m p hm hp hpm

example : 2 ∣ 12 / 2 ∧ 3 ∣ 12 / 2 :=
  ⟨g34s_half_exponent_no_prime 12 2 ⟨3, rfl⟩ Nat.prime_two ⟨6, rfl⟩,
    g34s_half_exponent_no_prime 12 3 ⟨3, rfl⟩ Nat.prime_three ⟨4, rfl⟩⟩

/-- Falsification check: `4 ∣ m` is needed; at `m = 6` the prime `2` does not divide `m/2`. -/
example : ¬ (2 ∣ 6 / 2) := by decide

/-! ## The bridge into the stage field -/

/-- **The stage field `fiber_alg` from the direct premise.** Proposition 4.6 and Corollary 4.7's
output, `g34s_Prop46 P`, is the field `∀ s, wtr_WeilAlg (P.fiber s)`.
Source: G34 v1.5, Proposition 4.6 (`prop:supply`) and Corollary 4.7 (`cor:everymember`), with
Theorem 5.1 (`thm:brauer`); Schoen, Compositio Math. 65 (1988), Theorem 2.0 and Corollary 3.1, with
G34 Lemma 4.4; Milne, Duke Math. J. 96 (1999), Theorem 3.2. -/
theorem g34s_fiber_alg (P : g34h_PrymFamily) (h46 : g34s_Prop46 P) :
    ∀ s, wtr_WeilAlg (P.fiber s) :=
  h46

/-- With the boundary stage: the supply premise fills `fiber_alg` of `g34h_RemainingFields`, and
`g34h_stageFields_partial` carries it into `wtr_StageFields`. -/
example (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (Φ : g34b_BoundaryPeriodMap F P.fiber) (h46 : g34s_Prop46 P)
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, HodgeLean.Foundations.IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    (g34h_stageFields_partial F P
      ⟨fun s _ => g34b_fiber_disc P.fiber (g34h_fiber_polarized P) hpar s,
        g34s_fiber_alg P h46, g34b_dominant F P.fiber Φ, spread, transport⟩).fiber_alg =
      g34s_fiber_alg P h46 :=
  rfl

end HodgeLean.Papers
