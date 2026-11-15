import HodgeLean.Papers.PapersArithmeticProofs

/-! # Compact results from the posted papers, batch 1: the arithmetic certificates (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-papers1.md`; see `docs/specs/PapersArithmetic.md`. Do
not edit this file. Each theorem is proved by the matching `_aux` theorem in
`PapersArithmeticProofs.lean`. The manuscripts are the read-only copies in
`docs/specs/inputs/papers/` (G32 v0.16, QI v0.7, G34 v1.5, TT v0.16), and every citation is a
printed number.

It claims, for printed data transcribed exactly (items 3, 4, 7, 8, 14 of
`docs/specs/inputs/papers/lean-compact-list.md`):

* item 3 (G32 Proposition 6.3): the printed 6×6 matrix `h_0` over `ℚ(ω)` is Hermitian, has the
  printed characteristic polynomial and its printed factorization, determinant `−2/81 = −2 Nm(1/9)`,
  six real characteristic roots (three positive, three negative), and signature `(3, 3)`;
* item 4 (QI Proposition 8.2, TT Section 11): the printed `h_0` over `ℚ(i)` is Hermitian with
  determinant `−3` and signature `(3, 3)`; `−3` is not `−1` times a norm from `ℚ(i)` (norms have
  even 3-adic valuation); TT's four determinants divided by `−3` are the printed norms;
* item 7 (G32 Lemma 3.6, G34 Lemma 9.1, QI Lemma 8.1): the multiplicity and Hodge-number arithmetic
  from the printed local monodromy (angles, branch orders), the genus `505 441`, and the defect
  identity in its arithmetic form;
* item 8 (G32 Table 1, QI Proposition 8.4, Table 4, Example 8.5): on every printed row
  `h = 2q − 2 + s` is positive and even and the exponents are simple; the printed slot data satisfy
  the product-admissibility bounds, and Example 8.5 balances at `t = 1, 5, 7, 11`;
* item 14 (G34 Lemma 10.1, Proposition 10.2): the class arithmetic in `ℚ^×/Nm K^×` for `E × Ē`, and
  the 2×2 determinant `|c|²(ι(α)² − ῑ(α)²)`, nonzero exactly when `α² ∉ ℚ`, with `α = 1 + ω`;
* falsification checks: a perturbed entry of either matrix changes its determinant (for QI, into
  the split class), and a non-simple exponent multiset fails simplicity.

It does not claim: that the printed matrices are the Gram matrices of the parabolic cup product
(G32 Lemma 6.2, QI Lemma 6.2) or of any abelian variety's Hermitian form (G32 Proposition 6.1); that
the printed angles, branch orders, table rows or slot data come from the groups (the GAP double
coset computations); the character identity (G32 Proposition 4.5) beyond the transcription check
`Σ|n_i| = 56`; the formulas of G32 Proposition 3.1 themselves (only their arithmetic is evaluated);
any discriminant, signature or Weil type of an abelian variety; or any algebraicity. Each statement
says what it checks about printed numbers. HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Papers

open Polynomial Matrix ComplexConjugate

/-! ## Item 3: G32 Proposition 6.3, the printed matrix over ℚ(ω) -/

/-- **The printed `h_0` is Hermitian.** For a complex cube root of unity `ω ≠ 1`, the matrix `h_0`
of
G32 Proposition 6.3 equals its conjugate transpose (`ω̄ = ω² = −1 − ω`).
Source: G32 v0.16 (`weil-nonsplit-g32-v0.16`), proof of Proposition 6.3. -/
theorem papers_g32_h0_isHermitian (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).IsHermitian :=
  papers_g32_h0_isHermitian_aux ω hω

example (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).IsHermitian :=
  papers_g32_h0_isHermitian ω hω

/-- **The printed factorization.** The printed characteristic polynomial factors as printed:
`x⁶ − 4/3 x⁵ − 26/9 x⁴ + 41/27 x³ + 19/27 x² − 22/81 x − 2/81 = (x² − 2/9)(x⁴ − 4/3 x³ − 8/3 x² +
11/9 x + 1/9)`.
Source: G32 v0.16, proof of Proposition 6.3. -/
theorem papers_g32_charpoly_factor :
    g32Charpoly = (X ^ 2 - C (2/9)) * (X ^ 4 - C (4/3) * X ^ 3 - C (8/3) * X ^ 2 + C (11/9) * X
      + C (1/9)) :=
  papers_g32_charpoly_factor_aux

example :
    g32Charpoly = (X ^ 2 - C (2/9)) * (X ^ 4 - C (4/3) * X ^ 3 - C (8/3) * X ^ 2 + C (11/9) * X
      + C (1/9)) :=
  papers_g32_charpoly_factor

/-- **The printed characteristic polynomial.** Over any field of characteristic zero and for any `ω`
with `ω² + ω + 1 = 0` (so over `ℚ(ω)`, `CyclotomicField 3 ℚ` or `ℂ`), the printed `h_0` has the
printed characteristic polynomial. This checks the printed matrix against the printed polynomial;
it does not check that `h_0` is the Gram matrix of the parabolic cup product (G32 Lemma 6.2).
Source: G32 v0.16, proof of Proposition 6.3. -/
theorem papers_g32_h0_charpoly {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).charpoly = g32Charpoly.map (algebraMap ℚ K) :=
  papers_g32_h0_charpoly_aux ω hω

example {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).charpoly = g32Charpoly.map (algebraMap ℚ K) :=
  papers_g32_h0_charpoly ω hω

/-- **The printed determinant.** The printed `h_0` has determinant `−2/81`.
Source: G32 v0.16, proof of Proposition 6.3. -/
theorem papers_g32_h0_det {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).det = -2/81 :=
  papers_g32_h0_det_aux ω hω

example {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).det = -2/81 :=
  papers_g32_h0_det ω hω

/-- **Six real roots, three of each sign.** The printed characteristic polynomial has six real roots
counted with multiplicity, three positive and three negative (printed: about `−1.326, −0.471,
−0.078, 0.471, 0.474, 2.263`).
Source: G32 v0.16, proof of Proposition 6.3. -/
theorem papers_g32_charpoly_realRoots :
    (realRoots g32Charpoly).card = 6 ∧ posRealRootCount g32Charpoly = 3 ∧
      negRealRootCount g32Charpoly = 3 :=
  papers_g32_charpoly_realRoots_aux

example :
    (realRoots g32Charpoly).card = 6 ∧ posRealRootCount g32Charpoly = 3 ∧
      negRealRootCount g32Charpoly = 3 :=
  papers_g32_charpoly_realRoots

/-- **Signature `(3, 3)`.** For a complex cube root of unity `ω ≠ 1`, the Hermitian matrix `h_0` has
three positive and three negative eigenvalues. This is the signature of the printed matrix, not a
statement about an abelian variety.
Source: G32 v0.16, proof of Proposition 6.3. -/
theorem papers_g32_h0_signature (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (Finset.univ.filter fun i =>
        0 < (papers_g32_h0_isHermitian ω hω).eigenvalues i).card = 3 ∧
      (Finset.univ.filter fun i =>
        (papers_g32_h0_isHermitian ω hω).eigenvalues i < 0).card = 3 :=
  papers_g32_h0_signature_aux ω hω

example (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (Finset.univ.filter fun i =>
        0 < (papers_g32_h0_isHermitian ω hω).eigenvalues i).card = 3 ∧
      (Finset.univ.filter fun i =>
        (papers_g32_h0_isHermitian ω hω).eigenvalues i < 0).card = 3 :=
  papers_g32_h0_signature ω hω

/-- **The class of the determinant.** `−2/81 = −2 · Nm(1/9)` for the norm of `ℚ(ω)`; equivalently
`−2/81` and `−2` have the same class in `ℚ^×/Nm K^×` for `K = ℚ(√−3)` (norm form `x² + 3y²`).
Source: G32 v0.16, proof of Proposition 6.3. -/
theorem papers_g32_det_norm :
    (-2/81 : ℚ) = -2 * normOmega (1/9) 0 ∧ SameNormClass 3 (-2/81) (-2) :=
  papers_g32_det_norm_aux

example :
    (-2/81 : ℚ) = -2 * normOmega (1/9) 0 ∧ SameNormClass 3 (-2/81) (-2) :=
  papers_g32_det_norm

/-- **Falsification check.** Changing the `(3, 3)` entry of `h_0` from `1/3` to `2/3` (the matrix
stays
Hermitian) changes the determinant to `−1/27 ≠ −2/81`.
Source: direct computation on the printed matrix of G32 v0.16, Proposition 6.3. -/
theorem papers_g32_h0_det_perturbed
    {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω + Matrix.single 2 2 (1/3)).det = -1/27 :=
  papers_g32_h0_det_perturbed_aux ω hω

example {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω + Matrix.single 2 2 (1/3)).det = -1/27 :=
  papers_g32_h0_det_perturbed ω hω

/-! ## Item 4: QI Proposition 8.2 and TT Section 11, the printed matrix over ℚ(i) -/

/-- **The printed `h_0` is Hermitian.** With `ι = i`, the matrix `h_0` of QI Proposition 8.2 equals
its conjugate transpose.
Source: QI v0.7 (`weil-qi-m3-v0.7`), proof of Proposition 8.2. -/
theorem papers_qi_h0_isHermitian :
    (qiH0 Complex.I).IsHermitian :=
  papers_qi_h0_isHermitian_aux

example :
    (qiH0 Complex.I).IsHermitian :=
  papers_qi_h0_isHermitian

/-- **The printed determinant.** Over any field of characteristic zero and for any `ι` with `ι² =
−1`,
the printed `h_0` has determinant `−3`.
Source: QI v0.7, proof of Proposition 8.2. -/
theorem papers_qi_h0_det {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι).det = -3 :=
  papers_qi_h0_det_aux ι hι

example {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι).det = -3 :=
  papers_qi_h0_det ι hι

/-- **Signature `(3, 3)`.** The Hermitian matrix `h_0` (with `ι = i`) has three positive and three
negative eigenvalues.
Source: QI v0.7, proof of Proposition 8.2. -/
theorem papers_qi_h0_signature :
    (Finset.univ.filter fun i => 0 < papers_qi_h0_isHermitian.eigenvalues i).card = 3 ∧
      (Finset.univ.filter fun i => papers_qi_h0_isHermitian.eigenvalues i < 0).card = 3 :=
  papers_qi_h0_signature_aux

example :
    (Finset.univ.filter fun i => 0 < papers_qi_h0_isHermitian.eigenvalues i).card = 3 ∧
      (Finset.univ.filter fun i => papers_qi_h0_isHermitian.eigenvalues i < 0).card = 3 :=
  papers_qi_h0_signature

/-- **Norms from `ℚ(i)` have even 3-adic valuation.** Since `3` is inert in `ℤ[i]`, a nonzero
`a² + b²` with `a, b ∈ ℚ` has even 3-adic valuation.
Source: QI v0.7, proof of Proposition 8.2; TT v0.16, Section 11 ("odd 3-adic valuation", "3 is
inert in ℚ(i)"). -/
theorem papers_normGaussian_padicValRat_even (a b : ℚ) (h : normGaussian a b ≠ 0) :
    Even (padicValRat 3 (normGaussian a b)) :=
  papers_normGaussian_padicValRat_even_aux a b h

example (a b : ℚ) (h : normGaussian a b ≠ 0) :
    Even (padicValRat 3 (normGaussian a b)) :=
  papers_normGaussian_padicValRat_even a b h

/-- **`[−3]` is not the split class.** `−3` is not `−1` times a norm from `ℚ(i)`.
Source: QI v0.7, proof of Proposition 8.2 ("The class of −3 in ℚ^×/Nm K^× is [−3]"); TT v0.16,
Section 11 ("not the split class [−1], since 3 is inert in ℚ(i)"). -/
theorem papers_qi_disc_not_split :
    ¬ SameNormClass 1 (-3) (-1) :=
  papers_qi_disc_not_split_aux

example :
    ¬ SameNormClass 1 (-3) (-1) :=
  papers_qi_disc_not_split

/-- **TT's four determinants are in the class `[−3]`.** Divided by `−3`, the printed determinants
`−24, −6/25, −3/2, −6` are the printed norms `Nm(2+2i) = 8`, `Nm((1+i)/5) = 2/25`,
`Nm((1+i)/2) = 1/2`, `Nm(1+i) = 2`.
Source: TT v0.16 (`transfer-theorem-v0.16`), Section 11 ("What is certified"). -/
theorem papers_tt_dets_norm :
    (-24 : ℚ) / (-3) = normGaussian 2 2 ∧ (-6/25 : ℚ) / (-3) = normGaussian (1/5) (1/5) ∧
      (-3/2 : ℚ) / (-3) = normGaussian (1/2) (1/2) ∧ (-6 : ℚ) / (-3) = normGaussian 1 1 :=
  papers_tt_dets_norm_aux

example :
    (-24 : ℚ) / (-3) = normGaussian 2 2 ∧ (-6/25 : ℚ) / (-3) = normGaussian (1/5) (1/5) ∧
      (-3/2 : ℚ) / (-3) = normGaussian (1/2) (1/2) ∧ (-6 : ℚ) / (-3) = normGaussian 1 1 :=
  papers_tt_dets_norm

/-- **Odd 3-adic valuation.** Each of TT's four determinants has 3-adic valuation `1`.
Source: TT v0.16, Section 11 ("all with odd 3-adic valuation"). -/
theorem papers_tt_dets_padicValRat :
    padicValRat 3 (-24) = 1 ∧ padicValRat 3 (-6/25) = 1 ∧ padicValRat 3 (-3/2) = 1 ∧
      padicValRat 3 (-6) = 1 :=
  papers_tt_dets_padicValRat_aux

example :
    padicValRat 3 (-24) = 1 ∧ padicValRat 3 (-6/25) = 1 ∧ padicValRat 3 (-3/2) = 1 ∧
      padicValRat 3 (-6) = 1 :=
  papers_tt_dets_padicValRat

/-- **TT's four determinants are not in the split class.**
Source: TT v0.16, Section 11. -/
theorem papers_tt_dets_not_split :
    ∀ d ∈ ([-24, -6/25, -3/2, -6] : List ℚ), ¬ SameNormClass 1 d (-1) :=
  papers_tt_dets_not_split_aux

example :
    ∀ d ∈ ([-24, -6/25, -3/2, -6] : List ℚ), ¬ SameNormClass 1 d (-1) :=
  papers_tt_dets_not_split

/-- **Falsification check.** Changing the `(1, 1)` entry of `h_0` from `−2` to `−1` (the matrix
stays
Hermitian) changes the determinant to `−2 = −1 · Nm(1+i)`, which is in the split class.
Source: direct computation on the printed matrix of QI v0.7, Proposition 8.2. -/
theorem papers_qi_h0_det_perturbed {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι + Matrix.single 0 0 1).det = -2 ∧ SameNormClass 1 (-2) (-1) :=
  papers_qi_h0_det_perturbed_aux ι hι

example {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι + Matrix.single 0 0 1).det = -2 ∧ SameNormClass 1 (-2) (-1) :=
  papers_qi_h0_det_perturbed ι hι

/-! ## Item 7: multiplicities and Hodge numbers from the local monodromy -/

/-- **The defect identity, arithmetic form.** `(r − 2)d − Σ_j (d − c_j) = −2d + Σ_j c_j`: the
dimension count in the proof of G32 Proposition 3.1 gives its first formula.
Source: G32 v0.16, proof of Proposition 3.1; TT v0.16, Proposition 2.1. -/
theorem papers_defect_identity (d : ℤ) (cs : List ℤ) :
    ((cs.length : ℤ) - 2) * d - (cs.map fun c => d - c).sum = -2 * d + cs.sum :=
  papers_defect_identity_aux d cs

example (d : ℤ) (cs : List ℤ) :
    ((cs.length : ℤ) - 2) * d - (cs.map fun c => d - c).sum = -2 * d + cs.sum :=
  papers_defect_identity d cs

/-- **G32 Lemma 3.6, the multiplicity.** From the angles of the class datum, `m_ρ = −8 + 12 + 2 =
6`.
Source: G32 v0.16, proof of Lemma 3.6. -/
theorem papers_g32_multiplicity :
    defectMultiplicity 4 g32Angles = -8 + 12 + 2 ∧ defectMultiplicity 4 g32Angles = 6 :=
  papers_g32_multiplicity_aux

example :
    defectMultiplicity 4 g32Angles = -8 + 12 + 2 ∧ defectMultiplicity 4 g32Angles = 6 :=
  papers_g32_multiplicity

/-- **G32 Lemma 3.6, the Hodge numbers.** `6 · 2/3 + 6 · 1/3 + 1 − 4 = 3`, and `6 − 3 = 3`.
Source: G32 v0.16, proof of Lemma 3.6. -/
theorem papers_g32_hodge :
    holomorphicMultiplicity 4 g32Angles = 6 * (2/3) + 6 * (1/3) + 1 - 4 ∧
      holomorphicMultiplicity 4 g32Angles = 3 ∧
      (defectMultiplicity 4 g32Angles : ℚ) - holomorphicMultiplicity 4 g32Angles = 3 :=
  papers_g32_hodge_aux

example :
    holomorphicMultiplicity 4 g32Angles = 6 * (2/3) + 6 * (1/3) + 1 - 4 ∧
      holomorphicMultiplicity 4 g32Angles = 3 ∧
      (defectMultiplicity 4 g32Angles : ℚ) - holomorphicMultiplicity 4 g32Angles = 3 :=
  papers_g32_hodge

/-- **G32 Lemma 3.6, the genus.** `2g − 2 = 155 520 (−2 + 12 · 2/3 + 1/2) = 1 010 880` with
`g = 505 441`.
Source: G32 v0.16, Lemma 3.6 and its proof. -/
theorem papers_g32_genus :
    riemannHurwitzEuler 155520 g32BranchOrders = 155520 * (-2 + 12 * (2/3) + 1/2) ∧
      riemannHurwitzEuler 155520 g32BranchOrders = 1010880 ∧
      riemannHurwitzEuler 155520 g32BranchOrders = 2 * 505441 - 2 :=
  papers_g32_genus_aux

example :
    riemannHurwitzEuler 155520 g32BranchOrders = 155520 * (-2 + 12 * (2/3) + 1/2) ∧
      riemannHurwitzEuler 155520 g32BranchOrders = 1010880 ∧
      riemannHurwitzEuler 155520 g32BranchOrders = 2 * 505441 - 2 :=
  papers_g32_genus

/-- **G34 Lemma 9.1.** `m_σ = −12 + 20 = 8` and `20 · 1/2 − 6 = 4` for each Hodge number.
Source: G34 v1.5 (`weil-qsqrt3-v1.5`), proof of Lemma 9.1. -/
theorem papers_g34_multiplicity_hodge :
    defectMultiplicity 6 g34Angles = -12 + 20 ∧ defectMultiplicity 6 g34Angles = 8 ∧
      holomorphicMultiplicity 6 g34Angles = 20 * (1/2) - 6 ∧
      holomorphicMultiplicity 6 g34Angles = 4 ∧
      (defectMultiplicity 6 g34Angles : ℚ) - holomorphicMultiplicity 6 g34Angles = 4 :=
  papers_g34_multiplicity_hodge_aux

example :
    defectMultiplicity 6 g34Angles = -12 + 20 ∧ defectMultiplicity 6 g34Angles = 8 ∧
      holomorphicMultiplicity 6 g34Angles = 20 * (1/2) - 6 ∧
      holomorphicMultiplicity 6 g34Angles = 4 ∧
      (defectMultiplicity 6 g34Angles : ℚ) - holomorphicMultiplicity 6 g34Angles = 4 :=
  papers_g34_multiplicity_hodge

/-- **QI Lemma 8.1, the two special points.** `c_σ(ix₁) = 4` with age `2`, and `c_σ(ix₂) = 8` with
angle sum `4`, as printed.
Source: QI v0.7, proof of Lemma 8.1. -/
theorem papers_qi_points :
    rankDefect qiAnglesIX1 = 4 ∧ age qiAnglesIX1 = 2 ∧ rankDefect qiAnglesIX2 = 8 ∧
      age qiAnglesIX2 = 4 :=
  papers_qi_points_aux

example :
    rankDefect qiAnglesIX1 = 4 ∧ age qiAnglesIX1 = 2 ∧ rankDefect qiAnglesIX2 = 8 ∧
      age qiAnglesIX2 = 4 :=
  papers_qi_points

/-- **QI Lemma 8.1.** `m_σ = −16 + 10 + 4 + 8 = 6`; the ages of the inverses total `22 − 11 = 11`,
so
the Hodge numbers are `11 − 8 = 3` and `6 − 3 = 3`.
Source: QI v0.7, proof of Lemma 8.1. -/
theorem papers_qi_multiplicity_hodge :
    defectMultiplicity 8 qiAngles = -16 + 10 + 4 + 8 ∧ defectMultiplicity 8 qiAngles = 6 ∧
      holomorphicMultiplicity 8 qiAngles = (22 - 11) - 8 ∧
      holomorphicMultiplicity 8 qiAngles = 3 ∧
      (defectMultiplicity 8 qiAngles : ℚ) - holomorphicMultiplicity 8 qiAngles = 3 :=
  papers_qi_multiplicity_hodge_aux

example :
    defectMultiplicity 8 qiAngles = -16 + 10 + 4 + 8 ∧ defectMultiplicity 8 qiAngles = 6 ∧
      holomorphicMultiplicity 8 qiAngles = (22 - 11) - 8 ∧
      holomorphicMultiplicity 8 qiAngles = 3 ∧
      (defectMultiplicity 8 qiAngles : ℚ) - holomorphicMultiplicity 8 qiAngles = 3 :=
  papers_qi_multiplicity_hodge

/-! ## Item 8: admissibility (G32 Table 1) and slot arithmetic (QI Proposition 8.4, Example 8.5) -/

/-- **Transcription check.** Table 1 has rows `1, …, 51`, and `Σ_i |n_i| = 56` as in G32
Proposition 4.5.
Source: G32 v0.16, Proposition 4.5 and Appendix B, Table 1. -/
theorem papers_g32_table_index :
    g32WitnessTable.map (·.i) = List.range' 1 51 ∧
      (g32WitnessTable.map fun r => r.n.natAbs).sum = 56 :=
  papers_g32_table_index_aux

example :
    g32WitnessTable.map (·.i) = List.range' 1 51 ∧
      (g32WitnessTable.map fun r => r.n.natAbs).sum = 56 :=
  papers_g32_table_index

/-- **Orders.** Every supplier of Table 1 has `m ∈ {3, 6, 12, 15}` (so `m ≥ 3` and `3 ∣ m`).
Source: G32 v0.16, Subsection 4.2 ("Every supplier of Table 1 has 3 ∣ m (m ∈ {3,6,12,15})"). -/
theorem papers_g32_table_m :
    ∀ r ∈ g32WitnessTable, r.m ∈ [3, 6, 12, 15] :=
  papers_g32_table_m_aux

example :
    ∀ r ∈ g32WitnessTable, r.m ∈ [3, 6, 12, 15] :=
  papers_g32_table_m

/-- **`h = 2q − 2 + s`** on every row of Table 1.
Source: G32 v0.16, Subsection 4.1 (Schoen, Lemma 1.5) and Appendix B, Table 1. -/
theorem papers_g32_table_h :
    ∀ r ∈ g32WitnessTable, (r.h : ℤ) = 2 * r.q - 2 + r.s :=
  papers_g32_table_h_aux

example :
    ∀ r ∈ g32WitnessTable, (r.h : ℤ) = 2 * r.q - 2 + r.s :=
  papers_g32_table_h

/-- **Branch points.** On every row the exponent counts sum to `s`, and every exponent lies in
`1, …, m − 1`.
Source: G32 v0.16, Appendix B, Table 1. -/
theorem papers_g32_table_s :
    ∀ r ∈ g32WitnessTable, (r.exps.map Prod.snd).sum = r.s ∧ ∀ p ∈ r.exps, 0 < p.1 ∧ p.1 < r.m :=
  papers_g32_table_s_aux

example :
    ∀ r ∈ g32WitnessTable, (r.exps.map Prod.snd).sum = r.s ∧ ∀ p ∈ r.exps, 0 < p.1 ∧ p.1 < r.m :=
  papers_g32_table_s

/-- **`h` is positive and even** on every row of Table 1.
Source: G32 v0.16, Appendix B ("h is even and positive"). -/
theorem papers_g32_table_h_pos_even :
    ∀ r ∈ g32WitnessTable, 0 < r.h ∧ Even r.h :=
  papers_g32_table_h_pos_even_aux

example :
    ∀ r ∈ g32WitnessTable, 0 < r.h ∧ Even r.h :=
  papers_g32_table_h_pos_even

/-- **The exponents are simple** on every row of Table 1 (Schoen's condition).
Source: G32 v0.16, Appendix B ("Every row is admissible") and Subsection 4.1. -/
theorem papers_g32_table_simple :
    ∀ r ∈ g32WitnessTable, IsSimpleExps r.m (expandExps r.exps) :=
  papers_g32_table_simple_aux

example :
    ∀ r ∈ g32WitnessTable, IsSimpleExps r.m (expandExps r.exps) :=
  papers_g32_table_simple

/-- **Column `d`.** On ramified rows `d = gcd(m, α)`; unramified rows print `--`.
Source: G32 v0.16, Appendix B, Table 1. -/
theorem papers_g32_table_d :
    ∀ r ∈ g32WitnessTable, r.d = if r.exps = [] then none else some (gcdExps r.m r.exps) :=
  papers_g32_table_d_aux

example :
    ∀ r ∈ g32WitnessTable, r.d = if r.exps = [] then none else some (gcdExps r.m r.exps) :=
  papers_g32_table_d

/-- **Column type.** A row is `U` exactly when `s = 0`, and `S*` exactly when it is ramified, `4 ∣
m`
and every exponent is `m/2` (the case of G32 Lemma 4.3).
Source: G32 v0.16, Subsection 4.1 (before Lemma 4.3) and Appendix B, Table 1. -/
theorem papers_g32_table_kind :
    ∀ r ∈ g32WitnessTable, (r.kind = .U ↔ r.s = 0) ∧
      (r.kind = .Sstar ↔ 0 < r.s ∧ 4 ∣ r.m ∧ ∀ p ∈ r.exps, 2 * p.1 = r.m) :=
  papers_g32_table_kind_aux

example :
    ∀ r ∈ g32WitnessTable, (r.kind = .U ↔ r.s = 0) ∧
      (r.kind = .Sstar ↔ 0 < r.s ∧ 4 ∣ r.m ∧ ∀ p ∈ r.exps, 2 * p.1 = r.m) :=
  papers_g32_table_kind

/-- **Falsification check.** The exponent multiset `{1, 1}` modulo `3` is not simple.
Source: Schoen's simplicity (G32 v0.16, Subsection 4.1); `1 + 1 ≢ 0 (mod 3)`. -/
theorem papers_not_simple :
    ¬ IsSimpleExps 3 [1, 1] :=
  papers_not_simple_aux

example :
    ¬ IsSimpleExps 3 [1, 1] :=
  papers_not_simple

/-- **QI Proposition 8.4 on Table 4.** Every row has `g_X ≥ 1`; every slot has order `4` or `12`, at
least `20` branch points, `e' = e/d` with `e' ∣ 12`, and `e' ∈ {4, 12}`.
Source: QI v0.7, Proposition 8.4, Definition 4.10 and Appendix C, Table 4. -/
theorem papers_qi_slots_admissible :
    ∀ row ∈ qiSlotTable, 1 ≤ row.genus ∧ ∀ sl ∈ row.slots, (sl.e = 4 ∨ sl.e = 12) ∧ 20 ≤ sl.s ∧
      sl.e' * sl.d = sl.e ∧ sl.e' ∣ 12 ∧ (sl.e' = 4 ∨ sl.e' = 12) :=
  papers_qi_slots_admissible_aux

example :
    ∀ row ∈ qiSlotTable, 1 ≤ row.genus ∧ ∀ sl ∈ row.slots, (sl.e = 4 ∨ sl.e = 12) ∧ 20 ≤ sl.s ∧
      sl.e' * sl.d = sl.e ∧ sl.e' ∣ 12 ∧ (sl.e' = 4 ∨ sl.e' = 12) :=
  papers_qi_slots_admissible

/-- **Slot counts.** The printed lifts have `2`, `4` and `45` slots.
Source: QI v0.7, Appendix C, Table 4. -/
theorem papers_qi_slots_count :
    qiSlotTable.map (fun r => r.slots.length) = [2, 4, 45] :=
  papers_qi_slots_count_aux

example :
    qiSlotTable.map (fun r => r.slots.length) = [2, 4, 45] :=
  papers_qi_slots_count

/-- **`h = 2g_X − 2 + s` for the `w₃` characters** (`g_X = 1 730 347`).
Source: QI v0.7, Appendix C, Table 4 and the paragraph after it. -/
theorem papers_qi_w3_h :
    ∀ p ∈ qiW3SH, p.2 = 2 * 1730347 - 2 + p.1 :=
  papers_qi_w3_h_aux

example :
    ∀ p ∈ qiW3SH, p.2 = 2 * 1730347 - 2 + p.1 :=
  papers_qi_w3_h

/-- **QI Example 8.5, `h = 2g_X − 2 + s`** for both slots (`g_X = 3259`).
Source: QI v0.7, Example 8.5. -/
theorem papers_qi_ex85_h :
    ∀ sl ∈ qiExample85, sl.h = 2 * 3259 - 2 + sl.s :=
  papers_qi_ex85_h_aux

example :
    ∀ sl ∈ qiExample85, sl.h = 2 * 3259 - 2 + sl.s :=
  papers_qi_ex85_h

/-- **QI Example 8.5, balance.** `Σ_k (2p_{k,t} − h_k) = 0` at `t = 1, 5, 7, 11`:
`(−4, −4, 4, 4) + (4, 4, −4, −4) = 0`.
Source: QI v0.7, Example 8.5 and Proposition 8.4. -/
theorem papers_qi_ex85_balance :
    sumImbalance (qiExample85.map (·.imbalance)) = [0, 0, 0, 0] :=
  papers_qi_ex85_balance_aux

example :
    sumImbalance (qiExample85.map (·.imbalance)) = [0, 0, 0, 0] :=
  papers_qi_ex85_balance

/-- **QI Example 8.5, the printed Hodge types and dimensions.** The types `(6622, 6626)` and
`(3270, 3266)` have sums `h₁, h₂` and differences the imbalances at `t = 1`; their product is
`(9892, 9892)` of degree `19 784`; the Fermat dimensions are `s − 2 = 6730, 18`, with types
`(3363, 3367)` and `(11, 7)` multiplying to `(3374, 3374)` in dimension `6748`; and the cone has
dimension `3374 + 2 · 3259 = 9892`.
Source: QI v0.7, Example 8.5. -/
theorem papers_qi_ex85_numerology :
    (6622 + 6626 : ℤ) = 13248 ∧ (6622 - 6626 : ℤ) = -4 ∧ (3270 + 3266 : ℤ) = 6536 ∧
      (3270 - 3266 : ℤ) = 4 ∧ (6622 + 3270 : ℤ) = 9892 ∧ (6626 + 3266 : ℤ) = 9892 ∧
      (13248 + 6536 : ℤ) = 19784 ∧ (6732 - 2 : ℤ) = 6730 ∧ (20 - 2 : ℤ) = 18 ∧
      (3363 + 11 : ℤ) = 3374 ∧ (3367 + 7 : ℤ) = 3374 ∧ (6730 + 18 : ℤ) = 2 * 3374 ∧
      (3374 + 2 * 3259 : ℤ) = 9892 ∧ (2 * 9892 : ℤ) = 19784 :=
  papers_qi_ex85_numerology_aux

example :
    (6622 + 6626 : ℤ) = 13248 ∧ (6622 - 6626 : ℤ) = -4 ∧ (3270 + 3266 : ℤ) = 6536 ∧
      (3270 - 3266 : ℤ) = 4 ∧ (6622 + 3270 : ℤ) = 9892 ∧ (6626 + 3266 : ℤ) = 9892 ∧
      (13248 + 6536 : ℤ) = 19784 ∧ (6732 - 2 : ℤ) = 6730 ∧ (20 - 2 : ℤ) = 18 ∧
      (3363 + 11 : ℤ) = 3374 ∧ (3367 + 7 : ℤ) = 3374 ∧ (6730 + 18 : ℤ) = 2 * 3374 ∧
      (3374 + 2 * 3259 : ℤ) = 9892 ∧ (2 * 9892 : ℤ) = 19784 :=
  papers_qi_ex85_numerology

/-! ## Item 14: G34 Lemma 10.1 and Proposition 10.2, the arithmetic core -/

/-- **G34 Lemma 10.1, the determinant and the class.** The form `(c) ⊕ (−cm)` has determinant
`−c²m`,
of class `[−m]` (for every `K = ℚ(√−D)`).
Source: G34 v1.5, proof of Lemma 10.1. -/
theorem papers_eebar_det (D c m : ℚ) (hc : c ≠ 0) :
    !![c, 0; 0, -(c * m)].det = -c ^ 2 * m ∧ SameNormClass D (-c ^ 2 * m) (-m) :=
  papers_eebar_det_aux D c m hc

example (D c m : ℚ) (hc : c ≠ 0) :
    !![c, 0; 0, -(c * m)].det = -c ^ 2 * m ∧ SameNormClass D (-c ^ 2 * m) (-m) :=
  papers_eebar_det D c m hc

/-- **Classes multiply.** The class in `ℚ^×/Nm K^×` of a product is the product of the classes (the
norm form is multiplicative).
Source: G34 v1.5, proof of Proposition 10.2 (`[t] ∏_j [−m_j]`); Brahmagupta's identity. -/
theorem papers_sameNormClass_mul
    (D a a' b b' : ℚ) (ha : SameNormClass D a a') (hb : SameNormClass D b b') :
    SameNormClass D (a * b) (a' * b') :=
  papers_sameNormClass_mul_aux D a a' b b' ha hb

example (D a a' b b' : ℚ) (ha : SameNormClass D a a') (hb : SameNormClass D b b') :
    SameNormClass D (a * b) (a' * b') :=
  papers_sameNormClass_mul D a a' b b' ha hb

/-- **G34 Proposition 10.2, the class arithmetic.** If `m₁` is in the class `[(−1)^{k+n}/t]`, then
`[t] [−m₁] [−1]^{k−1} = [(−1)^n]`.
Source: G34 v1.5, proof of Proposition 10.2 ("The product"). -/
theorem papers_compensation_class
    (D t m₁ : ℚ) (k n : ℕ) (hk : 1 ≤ k)
    (ht : t ≠ 0)     (hm : SameNormClass D m₁ ((-1) ^ (k + n) / t)) :
    SameNormClass D (t * (-m₁) * (-1) ^ (k - 1)) ((-1) ^ n) :=
  papers_compensation_class_aux D t m₁ k n hk ht hm

example
    (D t m₁ : ℚ) (k n : ℕ) (hk : 1 ≤ k)
    (ht : t ≠ 0)     (hm : SameNormClass D m₁ ((-1) ^ (k + n) / t)) :
    SameNormClass D (t * (-m₁) * (-1) ^ (k - 1)) ((-1) ^ n) :=
  papers_compensation_class D t m₁ k n hk ht hm

/-- **The class `[(−1)^{k+n}/t]` is positive** for `t < 0` and `k = n − 3`.
Source: G34 v1.5, proof of Proposition 10.2 ("that class is positive"). -/
theorem papers_compensation_positive (t : ℚ) (ht : t < 0) (n : ℕ) (hn : 3 ≤ n) :
    0 < (-1 : ℚ) ^ ((n - 3) + n) / t :=
  papers_compensation_positive_aux t ht n hn

example (t : ℚ) (ht : t < 0) (n : ℕ) (hn : 3 ≤ n) :
    0 < (-1 : ℚ) ^ ((n - 3) + n) / t :=
  papers_compensation_positive t ht n hn

/-- **A positive class has a positive integral representative**, because squares are norms.
Source: G34 v1.5, proof of Proposition 10.2. -/
theorem papers_positive_class_nat_rep (D q : ℚ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ SameNormClass D m q :=
  papers_positive_class_nat_rep_aux D q hq

example (D q : ℚ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ SameNormClass D m q :=
  papers_positive_class_nat_rep D q hq

/-- **G34 Proposition 10.2, the 2×2 determinant.** The coordinates `(c, c̄)` of `z₁` and
`(c ῑ(α)², conj(c ῑ(α)²))` of `z_α` have determinant `|c|² (ι(α)² − ῑ(α)²)`, with `ι(α) = α` and
`ῑ(α) = ᾱ`.
Source: G34 v1.5, proof of Proposition 10.2 ("Two independent classes"). -/
theorem papers_compensation_det (c α : ℂ) :
    !![c, conj c; c * conj α ^ 2, conj (c * conj α ^ 2)].det =
      (Complex.normSq c : ℂ) * (α ^ 2 - conj α ^ 2) :=
  papers_compensation_det_aux c α

example (c α : ℂ) :
    !![c, conj c; c * conj α ^ 2, conj (c * conj α ^ 2)].det =
      (Complex.normSq c : ℂ) * (α ^ 2 - conj α ^ 2) :=
  papers_compensation_det c α

/-- **Nonzero exactly when `α² ∉ ℚ`.** For `c ≠ 0` and `α = a + bω ∈ ℚ(ω) ⊂ ℂ`, the determinant is
nonzero if and only if `α²` is not rational.
Source: G34 v1.5, proof of Proposition 10.2 ("nonzero exactly when α² ∉ ℚ"). -/
theorem papers_compensation_det_ne_zero_iff
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (a b : ℚ) (c : ℂ) (hc : c ≠ 0) :
    !![c, conj c; c * conj ((a : ℂ) + b * ω) ^ 2, conj (c * conj ((a : ℂ) + b * ω) ^ 2)].det ≠ 0 ↔
      ∀ q : ℚ, ((a : ℂ) + b * ω) ^ 2 ≠ q :=
  papers_compensation_det_ne_zero_iff_aux ω hω a b c hc

example (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (a b : ℚ) (c : ℂ) (hc : c ≠ 0) :
    !![c, conj c; c * conj ((a : ℂ) + b * ω) ^ 2, conj (c * conj ((a : ℂ) + b * ω) ^ 2)].det ≠ 0 ↔
      ∀ q : ℚ, ((a : ℂ) + b * ω) ^ 2 ≠ q :=
  papers_compensation_det_ne_zero_iff ω hω a b c hc

/-- **The example `α = 1 + ω`.** `(1 + ω)² = ω`, which is not rational.
Source: G34 v1.5, proof of Proposition 10.2. -/
theorem papers_compensation_example (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (1 + ω) ^ 2 = ω ∧ ∀ q : ℚ, ω ≠ q :=
  papers_compensation_example_aux ω hω

example (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (1 + ω) ^ 2 = ω ∧ ∀ q : ℚ, ω ≠ q :=
  papers_compensation_example ω hω

end HodgeLean.Papers
