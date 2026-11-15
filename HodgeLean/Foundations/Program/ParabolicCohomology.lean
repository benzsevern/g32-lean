import HodgeLean.Foundations.Program.ParabolicCohomologyProofs
import HodgeLean.Foundations.Program.PrymVariation
import HodgeLean.Foundations.Program.PrymVariationLatticeArithmetic

/-! # PC stages H2 and H6: parabolic cocycles and the exact G32 root certificate (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-pc.md` (`docs/specs/ParabolicCohomology.md`). Do not
edit this file. Each theorem restates the matching `_aux` theorem in
`ParabolicCohomologyProofs.lean`.

**H2 (G32 Lemma 6.2 and Proposition 3.1, without topology).** For a tuple `T₁, …, T_r` of
matrices on `ι → K` with product one, over any field: the coboundaries and the tuples in
`Π_i ker(1 − T_i)` lie in `Z`; the corrected dimension formula
`dim V_par + Σ_i dim ker(T_i − 1) = (r − 2)·d + dim ⋂_i ker(T_i − 1) + dim ⋂_i ker(T_iᵀ − 1)`,
which for a tuple unitary for an invertible form becomes `(r − 2)·d + 2·dim V^G`; and, for an
invariant form `H`, the cup-product formula `S` is skew-Hermitian on `Z` and vanishes on the
trivial part in either slot, so that the descended pairing `pc_SPar` on `V_par` is `S` on any
representatives. The coefficients are the tuple itself on column vectors (for a
Nielsen tuple, `σ`), not its dual or its conjugate. The trivial tuple has `V_par = 0`, which
the uncorrected formula `(r − 2)·d − Σ_i dim ker(T_i − 1)` contradicts.

**H6.** For the thirteen-entry G32 root on `ℂ⁴` with the standard form: the local fixed
spaces have dimensions `3` (twelve reflections) and `2` (`x²`), the common fixed space is zero,
`dim V_par = 6`, and six explicit parameter tuples lie in `Z`, are independent modulo the
trivial part, and have `δ·S` Gram matrix exactly the printed `h_0` (`g32H0`), `δ = 1 + 2ω`.

**H6 over `K = ℚ(√−3)`.** The same root (`hp_rootTupleK`, the words of `b4b_root` in the
printed generators at `ζ = (−1 + √−3)/2`) and the same six tuples (`hp_certK`) over the field of
`g32d_ParabolicPolarization`: membership, the Gram identity, independence and `dim_K V_par = 6`,
and the statement that the embedding `hp_embed : K → ℂ` carries the `K`-data to the complex root
and certificate. A chain check builds a `K`-basis of `V_par` with Gram matrix `g32H0 ζ` for the
descended form `(1 + 2ζ)·pc_SPar`. The tuple is the repository's `b4b_root`; nothing here
identifies its Hurwitz component with the geometric family of the paper.

Not claimed: that `V_par` is the parabolic cohomology of a punctured sphere, that `S` is a cup
product, any comparison with the cohomology or the Hermitian form of a cover or of a Prym
factor (stages H3–H5), or the discriminant of any fibre (H7). The implication from H2, H6 and
H3–H5 to `hpol` is described in the spec document.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-! ## H2: the parameter model -/

/-- **Coboundaries and local kernels are parameters.** Under product one, the constant tuples
and the tuples in `Π_i ker(1 − T_i)` lie in `Z`.
Source: G32 v0.16, before Lemma 6.2; `Σ_i Q_i(1 − T_i) = 1 − T₁ ⋯ T_r` by telescoping. -/
theorem pc_trivialPart_le_Z {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) :
    pc_trivialPart T ≤ pc_Z T :=
  pc_trivialPart_le_Z_aux T hprod

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) :
    pc_trivialPart T ≤ pc_Z T :=
  pc_trivialPart_le_Z T hprod

/-- **The dimension formula, for any tuple with product one.**
`dim V_par + Σ_i dim ker(T_i − 1) = (r − 2)·d + dim ⋂_i ker(T_i − 1) + dim ⋂_i ker(T_iᵀ − 1)`,
with `d = |ι|`. No irreducibility, unitarity or nontriviality is assumed.
Source: G32 v0.16, Proposition 3.1 (first formula), corrected as in review hlean-rev-hps (H2);
rank–nullity for `a ↦ Σ_i Q_i(1 − T_i)a_i`, whose image has annihilator `⋂_i ker(T_iᵀ − 1)`. -/
theorem pc_finrank {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) :
    (Module.finrank K (pc_Vpar T) : ℤ) + ∑ i, (Module.finrank K (pc_localFixed T i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + Module.finrank K (pc_fixed T) +
        Module.finrank K (pc_fixedTranspose T) :=
  pc_finrank_aux T hprod

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (hprod : (List.ofFn T).prod = 1) :
    (Module.finrank K (pc_Vpar T) : ℤ) + ∑ i, (Module.finrank K (pc_localFixed T i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + Module.finrank K (pc_fixed T) +
        Module.finrank K (pc_fixedTranspose T) :=
  pc_finrank T hprod

/-- **Fixed rows and fixed columns have the same dimension** when every `T_i` preserves an
invertible sesquilinear form `H`: `v ↦ H⁻¹ (star v)` is a semilinear bijection between them.
Source: G32 v0.16, Proposition 3.1 (`H⁰(U₀, 𝕍^∨) = 0`, by unitarity). -/
theorem pc_finrank_fixedTranspose {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hH : IsUnit H.det) (hinv : ∀ i, (T i)ᴴ * H * T i = H) :
    Module.finrank K (pc_fixedTranspose T) = Module.finrank K (pc_fixed T) :=
  pc_finrank_fixedTranspose_aux T H hH hinv

example {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hH : IsUnit H.det) (hinv : ∀ i, (T i)ᴴ * H * T i = H) :
    Module.finrank K (pc_fixedTranspose T) = Module.finrank K (pc_fixed T) :=
  pc_finrank_fixedTranspose T H hH hinv

/-- **The dimension formula for a unitary tuple**, with the correction term:
`dim V_par + Σ_i dim ker(T_i − 1) = (r − 2)·d + 2·dim ⋂_i ker(T_i − 1)`.
Source: G32 v0.16, Proposition 3.1 (first formula; the paper assumes `τ` nontrivial, which
makes the last term zero), corrected as in review hlean-rev-hps (H2). -/
theorem pc_finrank_unitary {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hH : IsUnit H.det) (hinv : ∀ i, (T i)ᴴ * H * T i = H) :
    (Module.finrank K (pc_Vpar T) : ℤ) + ∑ i, (Module.finrank K (pc_localFixed T i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + 2 * Module.finrank K (pc_fixed T) :=
  pc_finrank_unitary_aux T H hprod hH hinv

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hH : IsUnit H.det) (hinv : ∀ i, (T i)ᴴ * H * T i = H) :
    (Module.finrank K (pc_Vpar T) : ℤ) + ∑ i, (Module.finrank K (pc_localFixed T i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + 2 * Module.finrank K (pc_fixed T) :=
  pc_finrank_unitary T H hprod hH hinv

/-- **The trivial-representation check.** For the constant tuple `T_i = 1` the parameter model
is zero, for every `r` and `d`. The uncorrected formula would give `(r − 2)·d − r·d = −2d`.
Source: review hlean-rev-hps (H2: "with every `T_i = 1`, parabolic cohomology is zero, while the
formula gives `−2d`"). -/
theorem pc_finrank_trivial (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (r : ℕ) : Module.finrank K (pc_Vpar (fun _ : Fin r => (1 : Matrix ι ι K))) = 0 :=
  pc_finrank_trivial_aux K ι r

example (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (r : ℕ) : Module.finrank K (pc_Vpar (fun _ : Fin r => (1 : Matrix ι ι K))) = 0 :=
  pc_finrank_trivial K ι r

/-- **Fixed vectors of a generating tuple are the invariants.** If the `g_i` generate `G`, then
`⋂_i ker(σ(g_i) − 1) = V^G`.
Source: G32 v0.16, §3.1 (Nielsen classes: `⟨g₁, …, g_r⟩ = G`) and Proposition 3.1. -/
theorem pc_fixed_tuple {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    pc_fixed (pc_tuple σ g) = pc_invariants σ :=
  pc_fixed_tuple_aux σ g hg

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    pc_fixed (pc_tuple σ g) = pc_invariants σ :=
  pc_fixed_tuple σ g hg

/-- **The dimension formula for a Nielsen tuple.** For a representation `σ` preserving an
invertible form and a generating tuple with `g₁ ⋯ g_r = 1`:
`dim V_par + Σ_i dim ker(σ(g_i) − 1) = (r − 2)·d + 2·dim V^G`. For `σ` nontrivial and
irreducible the last term is zero, which is the printed formula.
Source: G32 v0.16, Proposition 3.1 (first formula), corrected as in review hlean-rev-hps (H2);
G34 v1.5, Proposition 7.1. -/
theorem pc_finrank_nielsen {G : Type*} [Group G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (hH : IsUnit H.det)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) :
    (Module.finrank K (pc_Vpar (pc_tuple σ g)) : ℤ) +
        ∑ i, (Module.finrank K (pc_localFixed (pc_tuple σ g) i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + 2 * Module.finrank K (pc_invariants σ) :=
  pc_finrank_nielsen_aux σ g H hprod hg hH hinv

example {G : Type*} [Group G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (hH : IsUnit H.det)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) :
    (Module.finrank K (pc_Vpar (pc_tuple σ g)) : ℤ) +
        ∑ i, (Module.finrank K (pc_localFixed (pc_tuple σ g) i) : ℤ) =
      ((r : ℤ) - 2) * Fintype.card ι + 2 * Module.finrank K (pc_invariants σ) :=
  pc_finrank_nielsen σ g H hprod hg hH hinv

/-! ## H2: the cup-product formula -/

/-- **The printed formula without inverses.** For an invariant form,
`S(a, b) = Σ_i h(F^a_i + Q_i a_i, Q_i c^b_i)` for all parameters `a, b`.
Source: G32 v0.16, Lemma 6.2; `h(Q⁻¹x, y) = h(x, Qy)` for a `Q`-invariant form. -/
theorem pc_S_eq_invFree {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) :
    pc_S T H a b = pc_SInvFree T H a b :=
  pc_S_eq_invFree_aux T H hprod hinv a b

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) :
    pc_S T H a b = pc_SInvFree T H a b :=
  pc_S_eq_invFree T H hprod hinv a b

/-- **`S` is skew-Hermitian on `Z`**: `S(a, b) + conj S(b, a) = 0` for an invariant Hermitian
form. Off `Z` it fails in general.
Source: G32 v0.16, Lemma 6.2 and its proof (the telescoping
`h(F_{i+1}, F'_{i+1}) − h(F_i, F'_i)`, with `F₁ = 0 = F_{r+1}`). -/
theorem pc_S_skew {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) (ha : a ∈ pc_Z T) (hb : b ∈ pc_Z T) :
    pc_S T H a b + star (pc_S T H b a) = 0 :=
  pc_S_skew_aux T H hprod hHerm hinv a b ha hb

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) (ha : a ∈ pc_Z T) (hb : b ∈ pc_Z T) :
    pc_S T H a b + star (pc_S T H b a) = 0 :=
  pc_S_skew T H hprod hHerm hinv a b ha hb

/-- **`S` vanishes on the trivial part in the first slot**: `S(x, b) = 0` for `x` a coboundary
plus a tuple in `Π_i ker(1 − T_i)`, and `b ∈ Z`.
Source: G32 v0.16, Lemma 6.2 ("vanishes on coboundaries"; "does not depend on the choice of the
vectors `a_i`") and its proof. -/
theorem pc_S_trivialPart_left {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (x b : Fin r → ι → K) (hx : x ∈ pc_trivialPart T) (hb : b ∈ pc_Z T) :
    pc_S T H x b = 0 :=
  pc_S_trivialPart_left_aux T H hprod hinv x b hx hb

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (x b : Fin r → ι → K) (hx : x ∈ pc_trivialPart T) (hb : b ∈ pc_Z T) :
    pc_S T H x b = 0 :=
  pc_S_trivialPart_left T H hprod hinv x b hx hb

/-- **`S` vanishes on the trivial part in the second slot**, for `a ∈ Z` and an invariant
Hermitian form.
Source: G32 v0.16, Lemma 6.2 and its proof. -/
theorem pc_S_trivialPart_right {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a x : Fin r → ι → K) (ha : a ∈ pc_Z T) (hx : x ∈ pc_trivialPart T) :
    pc_S T H a x = 0 :=
  pc_S_trivialPart_right_aux T H hprod hHerm hinv a x ha hx

example {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a x : Fin r → ι → K) (ha : a ∈ pc_Z T) (hx : x ∈ pc_trivialPart T) :
    pc_S T H a x = 0 :=
  pc_S_trivialPart_right T H hprod hHerm hinv a x ha hx

/-- **The descended pairing on `V_par` is `S` on any representatives.** For product one and a
Hermitian invariant form, `pc_SPar` at the classes of `a, b ∈ Z` is `S(a, b)`, whatever
representatives `pc_lift` chose.
Source: G32 v0.16, Lemma 6.2 and proof of Proposition 6.3; `pc_S_trivialPart_left`,
`pc_S_trivialPart_right` and the sesquilinearity of `pc_SForm`. -/
theorem pc_SPar_mk {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) (ha : a ∈ pc_Z T) (hb : b ∈ pc_Z T) :
    pc_SPar T H (Submodule.Quotient.mk ⟨a, ha⟩) (Submodule.Quotient.mk ⟨b, hb⟩) =
      pc_S T H a b :=
  pc_SPar_mk_aux T H hprod hHerm hinv a b ha hb

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (hprod : (List.ofFn T).prod = 1) (hHerm : Hᴴ = H) (hinv : ∀ i, (T i)ᴴ * H * T i = H)
    (a b : Fin r → ι → K) (ha : a ∈ pc_Z T) (hb : b ∈ pc_Z T) :
    pc_SPar T H (Submodule.Quotient.mk ⟨a, ha⟩) (Submodule.Quotient.mk ⟨b, hb⟩) =
      pc_S T H a b :=
  pc_SPar_mk T H hprod hHerm hinv a b ha hb

/-! ### Satisfiable instances of the H2 hypotheses -/

/-- A nondegenerate instance over `ℚ`: four copies of `−1` on `ℚ¹` have product one and preserve
the standard form (here `V_par` has dimension `2`). -/
example :
    (List.ofFn fun _ : Fin 4 => (-1 : Matrix (Fin 1) (Fin 1) ℚ)).prod = 1 ∧
      IsUnit (1 : Matrix (Fin 1) (Fin 1) ℚ).det ∧
      (1 : Matrix (Fin 1) (Fin 1) ℚ)ᴴ = 1 ∧
      ∀ _ : Fin 4, (-1 : Matrix (Fin 1) (Fin 1) ℚ)ᴴ * 1 * (-1) = 1 := by
  refine ⟨?_, by simp, by simp, fun _ => by simp⟩
  simp [List.ofFn_succ]

/-- The G32 root tuple satisfies the H2 hypotheses with the standard form: product one (from
B6-3a's root products and `x⁴ = 1`) and unitarity (`b63l_toMatrix_mem_unitary`). -/
example :
    (List.ofFn hp_rootTuple).prod = 1 ∧ IsUnit (1 : Matrix (Fin 4) (Fin 4) ℂ).det ∧
      (1 : Matrix (Fin 4) (Fin 4) ℂ)ᴴ = 1 ∧
      ∀ j, (hp_rootTuple j)ᴴ * 1 * hp_rootTuple j = 1 := by
  refine ⟨?_, by simp, by simp, fun j => ?_⟩
  · have hsplit : List.ofFn b4b_root = (List.ofFn b4b_root).take 8 ++
        (((List.ofFn b4b_root).drop 8).take 4 ++ ((List.ofFn b4b_root).drop 8).drop 4) := by
      rw [List.take_append_drop, List.take_append_drop]
    have hlast : ((List.ofFn b4b_root).drop 8).drop 4 = [b4b_root 12] := by
      simp [List.ofFn_succ]
    have hroot : (List.ofFn b4b_root).prod = 1 := by
      rw [hsplit, List.prod_append, List.prod_append, b63_root_prefix_product,
        b63_root_tail_product, hlast]
      simp only [List.prod_cons, List.prod_nil, mul_one, one_mul]
      change b4b_generators 2 ^ 2 * b4b_generators 2 ^ 2 = 1
      rw [← pow_add]
      exact b63_generator_two_fourth
    have hmap : List.ofFn hp_rootTuple = (List.ofFn b4b_root).map b4b_toMatrix := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, ← map_list_prod, hroot, map_one]
  · rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)

/-! ## H6: the exact G32 root certificate -/

/-- **Local fixed spaces of the root.** Each of the twelve reflections fixes a hyperplane of
`ℂ⁴`, and `x²` fixes a plane.
Source: G32 v0.16, §3.3 and Appendix A (`c(r₁) = c(r₂) = 1`, `c(x²) = 2`); exact computation. -/
theorem hp_root_localFixed (j : Fin 13) :
    Module.finrank ℂ (pc_localFixed hp_rootTuple j) = if j = 12 then 2 else 3 :=
  hp_root_localFixed_aux j

example (j : Fin 13) :
    Module.finrank ℂ (pc_localFixed hp_rootTuple j) = if j = 12 then 2 else 3 :=
  hp_root_localFixed j

/-- **The root has no common fixed vector.**
Source: G32 v0.16, §3.1 and Appendix A (`σ` irreducible and nontrivial; the root generates,
`b63_root_generators`). -/
theorem hp_root_fixed : pc_fixed hp_rootTuple = ⊥ :=
  hp_root_fixed_aux

example : pc_fixed hp_rootTuple = ⊥ :=
  hp_root_fixed

/-- **The six certificate tuples are parameters**: each lies in `Z`.
Source: exact computation over `ℚ(ω)` (`docs/specs/ParabolicCohomology.md`, H6); G32 v0.16,
Lemma 6.2. -/
theorem hp_cert_mem (a : Fin 6) : hp_cert a ∈ pc_Z hp_rootTuple :=
  hp_cert_mem_aux a

example (a : Fin 6) : hp_cert a ∈ pc_Z hp_rootTuple :=
  hp_cert_mem a

/-- **The Gram matrix of `δ·S` on the six tuples is the printed `h_0`**, with `δ = 1 + 2ω` and
the standard form on `ℂ⁴`.
Source: exact computation over `ℚ(ω)` (`docs/specs/ParabolicCohomology.md`, H6); G32 v0.16,
Lemma 6.2 and Proposition 6.3 (the printed `h_0`). -/
theorem hp_cert_gram (a b : Fin 6) :
    (1 + 2 * HodgeLean.Papers.g32h_omega) * pc_S hp_rootTuple 1 (hp_cert a) (hp_cert b) =
      HodgeLean.Papers.g32H0 HodgeLean.Papers.g32h_omega a b :=
  hp_cert_gram_aux a b

example (a b : Fin 6) :
    (1 + 2 * HodgeLean.Papers.g32h_omega) * pc_S hp_rootTuple 1 (hp_cert a) (hp_cert b) =
      HodgeLean.Papers.g32H0 HodgeLean.Papers.g32h_omega a b :=
  hp_cert_gram a b

/-- **The six tuples are independent modulo the trivial part.**
Source: `hp_cert_gram`, `pc_S_trivialPart_right` and `det h_0 = −2/81 ≠ 0`
(`papers_g32_h0_det`). -/
theorem hp_cert_independent (c : Fin 6 → ℂ)
    (hc : ∑ a, c a • hp_cert a ∈ pc_trivialPart hp_rootTuple) : c = 0 :=
  hp_cert_independent_aux c hc

example (c : Fin 6 → ℂ)
    (hc : ∑ a, c a • hp_cert a ∈ pc_trivialPart hp_rootTuple) : c = 0 :=
  hp_cert_independent c hc

/-- **The parabolic model of the root has dimension six**: `11·4 − (12·3 + 2) + 2·0 = 6`.
Source: `pc_finrank_unitary`, `hp_root_localFixed`, `hp_root_fixed`; G32 v0.16, before
Proposition 6.1 (`prop:herm`: "a `K`-space of dimension six"). -/
theorem hp_vpar_finrank : Module.finrank ℂ (pc_Vpar hp_rootTuple) = 6 :=
  hp_vpar_finrank_aux

example : Module.finrank ℂ (pc_Vpar hp_rootTuple) = 6 :=
  hp_vpar_finrank

/-! ## H6 over `K = ℚ(√−3)` -/

/-- **The embedding sends `ζ` to `ω`**: `hp_embed ((−1 + √−3)/2) = e^{2πi/3}`.
Source: `hp_embed`; `g32h_omega = exp(2πi/3) = (−1 + i√3)/2`. -/
theorem hp_embed_zeta : hp_embed pc_zeta = HodgeLean.Papers.g32h_omega :=
  hp_embed_zeta_aux

example : hp_embed pc_zeta = HodgeLean.Papers.g32h_omega :=
  hp_embed_zeta

/-- **Extending scalars recovers the complex root.** The entrywise image of the `K`-tuple under
`hp_embed` is `hp_rootTuple`.
Source: `hp_rootTupleOver`, `b4b_root`; a ring map of fields commutes with the matrix inverse,
and the inverse in `b4b_Group` is the matrix inverse. -/
theorem hp_rootTupleK_map (j : Fin 13) :
    (hp_rootTupleK j).map hp_embed = hp_rootTuple j :=
  hp_rootTupleK_map_aux j

example (j : Fin 13) : (hp_rootTupleK j).map hp_embed = hp_rootTuple j :=
  hp_rootTupleK_map j

/-- **Extending scalars recovers the complex certificate.**
Source: `hp_certOver`, `hp_embed_zeta`. -/
theorem hp_certK_map (a : Fin 6) (j : Fin 13) (k : Fin 4) :
    hp_embed (hp_certK a j k) = hp_cert a j k :=
  hp_certK_map_aux a j k

example (a : Fin 6) (j : Fin 13) (k : Fin 4) : hp_embed (hp_certK a j k) = hp_cert a j k :=
  hp_certK_map a j k

/-- **The six certificate tuples are parameters over `K`.**
Source: exact computation over `ℚ(ω)` (`docs/specs/ParabolicCohomology.md`, H6); G32 v0.16,
Lemma 6.2. -/
theorem hp_certK_mem (a : Fin 6) : hp_certK a ∈ pc_Z hp_rootTupleK :=
  hp_certK_mem_aux a

example (a : Fin 6) : hp_certK a ∈ pc_Z hp_rootTupleK :=
  hp_certK_mem a

/-- **The Gram matrix over `K`**: `(1 + 2ζ)·S(hp_certK a, hp_certK b) = g32H0 ζ a b`, with the
standard form on `K⁴` and the involution of `K`.
Source: exact computation over `ℚ(ω)` (`docs/specs/ParabolicCohomology.md`, H6); G32 v0.16,
Lemma 6.2 and Proposition 6.3 (the printed `h_0`). -/
theorem hp_certK_gram (a b : Fin 6) :
    (1 + 2 * pc_zeta) * pc_S hp_rootTupleK 1 (hp_certK a) (hp_certK b) =
      HodgeLean.Papers.g32H0 pc_zeta a b :=
  hp_certK_gram_aux a b

example (a b : Fin 6) :
    (1 + 2 * pc_zeta) * pc_S hp_rootTupleK 1 (hp_certK a) (hp_certK b) =
      HodgeLean.Papers.g32H0 pc_zeta a b :=
  hp_certK_gram a b

/-- **The six tuples are independent modulo the trivial part over `K`.**
Source: `hp_certK_gram`, `pc_S_trivialPart_right` and `det h_0 = −2/81 ≠ 0`
(`papers_g32_h0_det`). -/
theorem hp_certK_independent (c : Fin 6 → hp_K)
    (hc : ∑ a, c a • hp_certK a ∈ pc_trivialPart hp_rootTupleK) : c = 0 :=
  hp_certK_independent_aux c hc

example (c : Fin 6 → hp_K)
    (hc : ∑ a, c a • hp_certK a ∈ pc_trivialPart hp_rootTupleK) : c = 0 :=
  hp_certK_independent c hc

/-- **The parabolic model of the `K`-root has dimension six over `K`.**
Source: `pc_finrank_unitary` over `K`; the local dimensions of `hp_root_localFixed`, which do not
change under the field extension `hp_embed`; G32 v0.16, before Proposition 6.1. -/
theorem hp_vparK_finrank : Module.finrank hp_K (pc_Vpar hp_rootTupleK) = 6 :=
  hp_vparK_finrank_aux

example : Module.finrank hp_K (pc_Vpar hp_rootTupleK) = 6 :=
  hp_vparK_finrank

/-! ## Chain checks -/

/-- Chain check: the dimension six follows from the corrected formula, the local fixed spaces
and the vanishing common fixed space. -/
example : Module.finrank ℂ (pc_Vpar hp_rootTuple) = 6 := by
  have hprod : (List.ofFn hp_rootTuple).prod = 1 := by
    have hsplit : List.ofFn b4b_root = (List.ofFn b4b_root).take 8 ++
        (((List.ofFn b4b_root).drop 8).take 4 ++ ((List.ofFn b4b_root).drop 8).drop 4) := by
      rw [List.take_append_drop, List.take_append_drop]
    have hlast : ((List.ofFn b4b_root).drop 8).drop 4 = [b4b_root 12] := by
      simp [List.ofFn_succ]
    have hroot : (List.ofFn b4b_root).prod = 1 := by
      rw [hsplit, List.prod_append, List.prod_append, b63_root_prefix_product,
        b63_root_tail_product, hlast]
      simp only [List.prod_cons, List.prod_nil, mul_one, one_mul]
      change b4b_generators 2 ^ 2 * b4b_generators 2 ^ 2 = 1
      rw [← pow_add]
      exact b63_generator_two_fourth
    have hmap : List.ofFn hp_rootTuple = (List.ofFn b4b_root).map b4b_toMatrix := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, ← map_list_prod, hroot, map_one]
  have hinv : ∀ j, (hp_rootTuple j)ᴴ * 1 * hp_rootTuple j = 1 := fun j => by
    rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  have h := pc_finrank_unitary hp_rootTuple 1 hprod (by simp) hinv
  have h0 : Module.finrank ℂ (pc_fixed hp_rootTuple) = 0 := by
    rw [hp_root_fixed]
    exact finrank_bot ℂ _
  simp only [hp_root_localFixed, h0, Fintype.card_fin] at h
  have hsum : ∑ j : Fin 13, (((if j = 12 then 2 else 3 : ℕ)) : ℤ) = 38 := by
    simp [Fin.sum_univ_succ]
  push_cast at h hsum
  omega

/-- Chain check toward `hpol` (`g32d_ParabolicPolarization`, which asks for a `K`-basis of the
fibre with Gram matrix a positive rational multiple of `g32H0 ζ`): the classes of the six
certificate tuples form a basis of the parabolic model of the root, on whose representatives
`δ·S` has Gram matrix exactly `g32H0 ω` (scale `1`). The basis is built here from the frozen
statements; transporting it to the fibre is stages H3–H5 and H7. -/
example : ∃ e : Module.Basis (Fin 6) ℂ (pc_Vpar hp_rootTuple),
    (∀ a, e a = Submodule.Quotient.mk ⟨hp_cert a, hp_cert_mem a⟩) ∧
      ∀ a b, (1 + 2 * HodgeLean.Papers.g32h_omega) *
          pc_S hp_rootTuple 1 (hp_cert a) (hp_cert b) =
        HodgeLean.Papers.g32H0 HodgeLean.Papers.g32h_omega a b := by
  let v : Fin 6 → pc_Vpar hp_rootTuple :=
    fun a => Submodule.Quotient.mk ⟨hp_cert a, hp_cert_mem a⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine congrFun (hp_cert_independent c ?_)
    have hmk : (Submodule.Quotient.mk (∑ a, c a • (⟨hp_cert a, hp_cert_mem a⟩ :
        pc_Z hp_rootTuple)) : pc_Vpar hp_rootTuple) = 0 := by
      rw [← hc]
      change Submodule.mkQ _ (∑ a, c a • _) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hmk
    simpa using hmk
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, hp_vpar_finrank]), fun a => ?_, hp_cert_gram⟩
  simp [v]

/-- Chain check toward `hpol` over `K` (the field, basis and Gram shape of
`g32d_ParabolicPolarization`, with scale `c = 1`): the classes of `hp_certK` form a `K`-basis of
the parabolic model of the `K`-root, and the descended form `(1 + 2ζ)·pc_SPar` has Gram matrix
`g32H0 ζ` in it. Product one and unitarity over `K` are transported from `ℂ` through
`hp_rootTupleK_map`. Transporting the basis to the fibre is stages H3–H5 and H7. -/
example : ∃ e : Module.Basis (Fin 6) hp_K (pc_Vpar hp_rootTupleK),
    (∀ a, e a = Submodule.Quotient.mk ⟨hp_certK a, hp_certK_mem a⟩) ∧
      LinearMap.toMatrix₂ e e ((1 + 2 * pc_zeta) • pc_SPar hp_rootTupleK 1) =
        ((1 : ℚ) : hp_K) • HodgeLean.Papers.g32H0 pc_zeta := by
  have hinj : Function.Injective
      (hp_embed.mapMatrix : Matrix (Fin 4) (Fin 4) hp_K →+* Matrix (Fin 4) (Fin 4) ℂ) :=
    fun A B h => Matrix.ext fun i j => hp_embed.injective (congrFun (congrFun h i) j)
  have hmap : ∀ j, hp_embed.mapMatrix (hp_rootTupleK j) = hp_rootTuple j := hp_rootTupleK_map
  have hprodC : (List.ofFn hp_rootTuple).prod = 1 := by
    have hsplit : List.ofFn b4b_root = (List.ofFn b4b_root).take 8 ++
        (((List.ofFn b4b_root).drop 8).take 4 ++ ((List.ofFn b4b_root).drop 8).drop 4) := by
      rw [List.take_append_drop, List.take_append_drop]
    have hlast : ((List.ofFn b4b_root).drop 8).drop 4 = [b4b_root 12] := by
      simp [List.ofFn_succ]
    have hroot : (List.ofFn b4b_root).prod = 1 := by
      rw [hsplit, List.prod_append, List.prod_append, b63_root_prefix_product,
        b63_root_tail_product, hlast]
      simp only [List.prod_cons, List.prod_nil, mul_one, one_mul]
      change b4b_generators 2 ^ 2 * b4b_generators 2 ^ 2 = 1
      rw [← pow_add]
      exact b63_generator_two_fourth
    have hmapC : List.ofFn hp_rootTuple = (List.ofFn b4b_root).map b4b_toMatrix := by
      rw [List.map_ofFn]
      rfl
    rw [hmapC, ← map_list_prod, hroot, map_one]
  have hprod : (List.ofFn hp_rootTupleK).prod = 1 := by
    apply hinj
    rw [map_list_prod, List.map_ofFn, map_one]
    convert hprodC using 2
    exact congrArg List.ofFn (funext hmap)
  have hstar : Function.Semiconj hp_embed star star := by
    intro x
    simp only [hp_embed, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      QuadraticAlgebra.lift_apply_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      zero_mul, add_zero]
    simp [Rat.smul_def]
  have hinv : ∀ j, (hp_rootTupleK j)ᴴ * 1 * hp_rootTupleK j = 1 := fun j => by
    apply hinj
    rw [Matrix.mul_one, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.conjTranspose_map _ hstar]
    have := hmap j
    rw [RingHom.mapMatrix_apply] at this
    rw [this, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  let v : Fin 6 → pc_Vpar hp_rootTupleK :=
    fun a => Submodule.Quotient.mk ⟨hp_certK a, hp_certK_mem a⟩
  have hli : LinearIndependent hp_K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine congrFun (hp_certK_independent c ?_)
    have hmk : (Submodule.Quotient.mk (∑ a, c a • (⟨hp_certK a, hp_certK_mem a⟩ :
        pc_Z hp_rootTupleK)) : pc_Vpar hp_rootTupleK) = 0 := by
      rw [← hc]
      change Submodule.mkQ _ (∑ a, c a • _) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hmk
    simpa using hmk
  let e := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, hp_vparK_finrank])
  have he : ∀ a, e a = v a := fun a => by simp [e]
  refine ⟨e, he, Matrix.ext fun a b => ?_⟩
  rw [map_smul, Matrix.smul_apply, LinearMap.toMatrix₂_apply, he, he, Matrix.smul_apply,
    pc_SPar_mk hp_rootTupleK 1 hprod (by simp) hinv, ← hp_certK_gram a b]
  simp

end HodgeLean.Foundations.Program
