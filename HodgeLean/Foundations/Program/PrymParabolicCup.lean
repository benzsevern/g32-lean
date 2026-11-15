import HodgeLean.Foundations.Program.PrymParabolicCupProofs

/-! # Stage H4, algebraic part: the cup form on `H¹_σ` and the passage to `K = ℚ(√−3)` (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h4.md` (`docs/specs/PrymParabolicCup.md`). Do not edit
this file. Each theorem restates the matching `_aux` theorem in `PrymParabolicCupProofs.lean`.

**Claimed (once the bodies are proved).** On the explicit lifted complex `X̃(g)` of stage H3a, for a
finite group `G`, a tuple `g`, a field `K` with an involution and a representation
`σ : G →* Matrix ι ι K`:
- the cellular cup product evaluated on the orientation chain vanishes when the first argument is a
  coboundary and the second a cocycle (any tuple), and when the first is a cocycle and the second a
  coboundary (product one); any fibre matrix `H`;
- hence, under product one, the cup form `hg4_cupH1` on `H¹_σ = hg_eqH1 σ g` is the cochain form on
  any representatives;
- under product one, the map `V_par(pc_tuple σ g) → H¹_σ` induced by the Shapiro map is bijective,
  and for a Hermitian `σ`-invariant `H` it carries `|G|·pc_SPar` to `hg4_cupH1`: on the `σ`-isotypic
  part the cup form is H2's form, up to the positive rational scale `|G|`;
- the formula `pc_S` commutes with every star-compatible ring map of fields (base change, and
  complex conjugation, which replaces `σ` by `σ̄`).
For G32: a `K`-form `hg4_sigmaK` of the defining representation of `b4b_Group`, which `hp_embed`
carries to `b4b_toMatrix`, whose root tuple is H6's `hp_rootTupleK`, and whose character at the first
root entry is `3 + ζ`. The chain checks give a `K`-basis of `H¹_σ` of the `K`-form in which
`(1 + 2ζ)·hg4_cupH1` has Gram matrix `|G|·g32H0 ζ`, the shape of `g32d_ParabolicPolarization` with
`c = |G|`; and they record that the conjugate embedding of `K` gives `σ̄`, whose character differs,
and the conjugate Gram matrix `g32H0 ω̄`.

**Not claimed.** That `hg4_cupH1` is the intersection form on `H₁` of the actual cover `C_t`, up to
the sign of the orientation chain (the geometric half of H4, which needs H3b's realization,
monodromy and cellular–singular comparison, and Poincaré duality on the explicit surface); that
`H¹_σ` is the Prym lattice of a fibre (H5); any discriminant (H7). The statements are an
implication from the stated algebraic hypotheses only. The G32 tuple is the repository's
`b4b_root`; nothing here identifies it with the monodromy at the paper's base point `C₀`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-! ## Descent of the cup form -/

/-- **A coboundary in the first slot pairs to zero with a cocycle.** For any tuple, any fibre
matrix `H`, any `0`-cochain `φ` and any `1`-cocycle `β`:
`⟨δφ ∪ β, Σ_x Σ_i (A_i(x) − B_i(x))⟩ = 0`. With `(φ ∪ β)(ε) = h(φ(src ε), β(ε))`, the Leibniz rule
reads `δ(φ ∪ β)(τ) = (δφ ∪ β)(τ) + h(φ(v₀), δβ(τ))`; it uses only `src face₀ = tgt face₂` and
`src face₁ = src face₂`, which hold on every triangle, and `hg_fundEval_delta1`.
Source: Hatcher, *Algebraic Topology*, §3.2 (the coboundary formula for the cup product);
`hg_fundEval_delta1`. -/
theorem hg4_cup_coboundary_left {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K)
    (φ : hg_Vert g → ι → K) (β : hg_Edge G r → ι → K)
    (hβ : β ∈ LinearMap.ker (hg_delta1 K (ι → K) g)) :
    hg4_cupForm g H (hg_delta0 K (ι → K) g φ) β = 0 :=
  hg4_cup_coboundary_left_aux g H φ β hβ

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K)
    (φ : hg_Vert g → ι → K) (β : hg_Edge G r → ι → K)
    (hβ : β ∈ LinearMap.ker (hg_delta1 K (ι → K) g)) :
    hg4_cupForm g H (hg_delta0 K (ι → K) g φ) β = 0 :=
  hg4_cup_coboundary_left g H φ β hβ

/-- **A coboundary in the second slot pairs to zero with a cocycle**, when `g₀ ⋯ g_{r−1} = 1`. With
`(α ∪ φ)(ε) = h(α(ε), φ(tgt ε))`, `δ(α ∪ φ)(τ) = h(δα(τ), φ(v₂)) − (α ∪ δφ)(τ)`; it uses
`tgt face₀ = tgt face₁`, which on `B_{r−1}(x)` is `b_∞(x (g₀ ⋯ g_{r−1})⁻¹) = b_∞(x)`.
Source: Hatcher, §3.2; `hg_fundEval_delta1`; G32 v0.16, §3.1 (the product relation). -/
theorem hg4_cup_coboundary_right {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (α : hg_Edge G r → ι → K)
    (hα : α ∈ LinearMap.ker (hg_delta1 K (ι → K) g)) (φ : hg_Vert g → ι → K) :
    hg4_cupForm g H α (hg_delta0 K (ι → K) g φ) = 0 :=
  hg4_cup_coboundary_right_aux g hprod H α hα φ

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (α : hg_Edge G r → ι → K)
    (hα : α ∈ LinearMap.ker (hg_delta1 K (ι → K) g)) (φ : hg_Vert g → ι → K) :
    hg4_cupForm g H α (hg_delta0 K (ι → K) g φ) = 0 :=
  hg4_cup_coboundary_right g hprod H α hα φ

/-- **The cup form on `H¹_σ` is the cochain form on any representatives**, under product one and for
any fibre matrix `H`. From the two previous statements and `hg_delta_comp` (the representatives
differ by coboundaries of equivariant `0`-cochains, and a cocycle plus a coboundary is a cocycle).
Source: Hatcher, §3.2 (the cup product on cohomology); `hg4_cup_coboundary_left`,
`hg4_cup_coboundary_right`. -/
theorem hg4_cupH1_mk {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (α β : hg_eqCocycles σ g) :
    hg4_cupH1 σ g H (Submodule.Quotient.mk α) (Submodule.Quotient.mk β) =
      hg4_cupForm g H α β :=
  hg4_cupH1_mk_aux σ g hprod H α β

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (α β : hg_eqCocycles σ g) :
    hg4_cupH1 σ g H (Submodule.Quotient.mk α) (Submodule.Quotient.mk β) =
      hg4_cupForm g H α β :=
  hg4_cupH1_mk σ g hprod H α β

/-! ## The `σ`-isotypic part and H2's form -/

/-- **Shapiro's lemma on classes.** Under product one, the map `V_par(pc_tuple σ g) → H¹_σ(X̃(g))`
induced by the explicit Shapiro map is bijective. Injective by `hg_shapiro_coboundary_iff`,
surjective by `hg_shapiro_surjective` (H3a's first chain check, as a statement about
`hg4_shapiroH1`).
Source: Brown, *Cohomology of Groups*, Chapter III, §5 (Shapiro's lemma); G32 v0.16, Lemma 6.2;
`hg_shapiro_coboundary_iff`, `hg_shapiro_surjective`. -/
theorem hg4_shapiroH1_bijective {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) :
    Function.Bijective (hg4_shapiroH1 σ g) :=
  hg4_shapiroH1_bijective_aux σ g hprod

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) :
    Function.Bijective (hg4_shapiroH1 σ g) :=
  hg4_shapiroH1_bijective σ g hprod

/-- **On the `σ`-isotypic part the cup form is `|G|` times H2's form.** For a finite group, product
one and a Hermitian `σ`-invariant `H`: `hg4_cupH1 (Φx) (Φy) = |G|·pc_SPar x y` for all classes
`x, y ∈ V_par`. From `hg4_cupH1_mk`, `hg_cup_shapiro` (`−|G|·conj S(b, a)` on representatives) and
`pc_S_skew` (on `Z`, `−conj S(b, a) = S(a, b)`). The scale `|G|` is a positive rational.
Source: G32 v0.16, proof of Lemma 6.2 and lines 537–548 (the comparison up to a rational scale);
`hg_cup_shapiro`, `pc_S_skew`. -/
theorem hg4_cupH1_shapiro {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K)
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (hHerm : Hᴴ = H)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) (x y : pc_Vpar (pc_tuple σ g)) :
    hg4_cupH1 σ g H (hg4_shapiroH1 σ g x) (hg4_shapiroH1 σ g y) =
      (Fintype.card G : K) * pc_SPar (pc_tuple σ g) H x y :=
  hg4_cupH1_shapiro_aux σ g hprod H hHerm hinv x y

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K)
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (hHerm : Hᴴ = H)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) (x y : pc_Vpar (pc_tuple σ g)) :
    hg4_cupH1 σ g H (hg4_shapiroH1 σ g x) (hg4_shapiroH1 σ g y) =
      (Fintype.card G : K) * pc_SPar (pc_tuple σ g) H x y :=
  hg4_cupH1_shapiro σ g hprod H hHerm hinv x y

/-! ## Change of field and conjugation -/

/-- **`pc_S` commutes with star-compatible ring maps of fields.** For `f : K →+* L` with
`f (star t) = star (f t)`, any tuple `T`, any `H` and all parameters:
`f (S_{T,H}(a, b)) = S_{f(T), f(H)}(f(a), f(b))`, entrywise. The matrix inverse in `pc_S` commutes
with `f` (`det` and the adjugate do, and `f` is injective). For `f = hp_embed` this is the passage
from `K` to `ℂ`; for `f = starRingEnd ℂ` it replaces `σ` by `σ̄`, `H` by `H̄` and `S` by `conj S`.
Source: G32 v0.16, Lemma 6.2 (the formula is polynomial in the entries and the involution);
Bourbaki, *Algebra*, Chapter III, §8 (the determinant and the adjugate commute with ring maps). -/
theorem hg4_pcS_map {K L : Type*} [Field K] [StarRing K] [Field L] [StarRing L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (f : K →+* L)
    (hf : ∀ t, f (star t) = star (f t)) (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (a b : Fin r → ι → K) :
    f (pc_S T H a b) =
      pc_S (fun i => (T i).map f) (H.map f) (fun i k => f (a i k)) (fun i k => f (b i k)) :=
  hg4_pcS_map_aux f hf T H a b

example {K L : Type*} [Field K] [StarRing K] [Field L] [StarRing L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (f : K →+* L)
    (hf : ∀ t, f (star t) = star (f t)) (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (a b : Fin r → ι → K) :
    f (pc_S T H a b) =
      pc_S (fun i => (T i).map f) (H.map f) (fun i k => f (a i k)) (fun i k => f (b i k)) :=
  hg4_pcS_map f hf T H a b

/-- **The `K`-form of `σ` gives `σ` under `hp_embed`.** For every `x ∈ b4b_Group`, the entrywise
image of `hg4_sigmaK x` under `hp_embed` is `b4b_toMatrix x`.
Source: `hg4_sigmaK` (the inverse of the entrywise `hp_embed` on `hg4_groupK`),
`hg4_groupK_map`. -/
theorem hg4_sigmaK_map (x : b4b_Group) : (hg4_sigmaK x).map hp_embed = b4b_toMatrix x :=
  hg4_sigmaK_map_aux x

example (x : b4b_Group) : (hg4_sigmaK x).map hp_embed = b4b_toMatrix x :=
  hg4_sigmaK_map x

/-- **The root tuple of the `K`-form is H6's `K`-tuple**: `hg4_sigmaK (b4b_root j) = hp_rootTupleK j`
for every `j`. Both map to `hp_rootTuple j` under the injective `hp_embed` (`hg4_sigmaK_map`,
`hp_rootTupleK_map`).
Source: `hp_rootTupleK`, `hp_rootTupleK_map`; G32 v0.16, Appendix A. -/
theorem hg4_sigmaK_tuple : pc_tuple hg4_sigmaK b4b_root = hp_rootTupleK :=
  hg4_sigmaK_tuple_aux

example : pc_tuple hg4_sigmaK b4b_root = hp_rootTupleK :=
  hg4_sigmaK_tuple

/-- **The character of the `K`-form at the first root entry is `3 + ζ`**: `hg4_sigmaK (b4b_root 0)`
is the printed reflection `r₁` at `ζ`, with diagonal `(ζ + 2)/3, (ζ + 2)/3, 1, (ζ + 2)/3`. Its
images `3 + ω` under `hp_embed` and `3 + ω̄` under the conjugate embedding differ, so the two
embeddings of `K` give `σ` and `σ̄`, which are not isomorphic.
Source: G32 v0.16, Appendix A (`r₁`, the reflection of class `𝓡₁` with eigenvalue `ω`);
`hp_rootTupleOver`. -/
theorem hg4_sigmaK_trace : Matrix.trace (hg4_sigmaK (b4b_root 0)) = 3 + pc_zeta :=
  hg4_sigmaK_trace_aux

example : Matrix.trace (hg4_sigmaK (b4b_root 0)) = 3 + pc_zeta :=
  hg4_sigmaK_trace

/-! ## Satisfiable instances -/

/-- The sign character of `ℤˣ = {±1}` on `ℚ¹`. -/
private def hg4_signRep : ℤˣ →* Matrix (Fin 1) (Fin 1) ℚ :=
  (Matrix.scalar (Fin 1) : ℚ →+* Matrix (Fin 1) (Fin 1) ℚ).toMonoidHom.comp
    ((Int.castRingHom ℚ).toMonoidHom.comp (Units.coeHom ℤ))

private theorem hg4_signRep_neg_one : hg4_signRep (-1) = -1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [hg4_signRep]

private theorem hg4_signRep_inv (x : ℤˣ) : (hg4_signRep x)ᴴ * 1 * hg4_signRep x = 1 := by
  rcases Int.units_eq_one_or x with rfl | rfl
  · simp
  · rw [hg4_signRep_neg_one]
    simp

/-- A nondegenerate instance of the generic statements (elliptic double cover): `G = ℤˣ` of order
two, the tuple `(−1, −1, −1, −1)` with product one, the sign character (not trivial) with the
invariant Hermitian form `1`. The cup form on `H¹_σ` is not zero: at the classes of
`a = (0, 1, 1, 0)` and `b = (1, 1, 0, 0)` it takes the value `|G|·S(a, b) = 2·2 = 4`, by
`hg4_cupH1_shapiro` and `pc_SPar_mk`; so `H¹_σ ≠ 0`. -/
example :
    (List.ofFn fun _ : Fin 4 => (-1 : ℤˣ)).prod = 1 ∧ hg4_signRep (-1) ≠ 1 ∧
      ∃ x y : pc_Vpar (pc_tuple hg4_signRep fun _ : Fin 4 => (-1 : ℤˣ)),
        hg4_cupH1 hg4_signRep (fun _ : Fin 4 => (-1 : ℤˣ)) 1
          (hg4_shapiroH1 hg4_signRep _ x) (hg4_shapiroH1 hg4_signRep _ y) = 4 := by
  have hT : ∀ i, pc_tuple hg4_signRep (fun _ : Fin 4 => (-1 : ℤˣ)) i = -1 :=
    fun _ => hg4_signRep_neg_one
  have hprod : (List.ofFn fun _ : Fin 4 => (-1 : ℤˣ)).prod = 1 := by simp [List.ofFn_succ]
  have hprodT : (List.ofFn (pc_tuple hg4_signRep fun _ : Fin 4 => (-1 : ℤˣ))).prod = 1 := by
    simp [List.ofFn_succ, hT]
  let a : Fin 4 → Fin 1 → ℚ := ![0, 1, 1, 0]
  let b : Fin 4 → Fin 1 → ℚ := ![1, 1, 0, 0]
  have hQ : ∀ i, pc_Q (pc_tuple hg4_signRep fun _ : Fin 4 => (-1 : ℤˣ)) i =
      (-1) ^ (i : ℕ) := by
    intro i
    fin_cases i <;> (simp [pc_Q, hT, List.finRange_succ, List.filter]; try norm_num)
  have ha : a ∈ pc_Z (pc_tuple hg4_signRep fun _ : Fin 4 => (-1 : ℤˣ)) := by
    show pc_relation _ a = 0
    simp only [pc_relation, LinearMap.coe_mk, AddHom.coe_mk, pc_c, hT, hQ, Fin.sum_univ_four]
    ext k
    fin_cases k
    simp [a, Matrix.mulVec, dotProduct, pow_succ]
  have hb : b ∈ pc_Z (pc_tuple hg4_signRep fun _ : Fin 4 => (-1 : ℤˣ)) := by
    show pc_relation _ b = 0
    simp only [pc_relation, LinearMap.coe_mk, AddHom.coe_mk, pc_c, hT, hQ, Fin.sum_univ_four]
    ext k
    fin_cases k
    simp [b, Matrix.mulVec, dotProduct, pow_succ]
  refine ⟨hprod, ?_, Submodule.Quotient.mk ⟨a, ha⟩, Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
  · rw [hg4_signRep_neg_one]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this
  · rw [hg4_cupH1_shapiro hg4_signRep _ hprod 1 (by simp) hg4_signRep_inv,
      pc_SPar_mk _ 1 hprodT (by simp) (fun i => hg4_signRep_inv _) a b ha hb]
    simp only [pc_S, pc_F, pc_c, hT, hQ, Fin.sum_univ_four, Fintype.card_units_int]
    simp [a, b, Matrix.mulVec, dotProduct, Finset.sum_filter, Fin.sum_univ_four]
    norm_num

/-- The G32 hypotheses over `K`: product one of the root, and unitarity of the `K`-form for the
standard form (transported through the injective `hp_embed` from `b63l_toMatrix_mem_unitary`,
using `hg4_sigmaK_map`). -/
example : (List.ofFn b4b_root).prod = 1 ∧ ∀ x, (hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x = 1 := by
  refine ⟨b63d_root_product, fun x => ?_⟩
  have hstar : Function.Semiconj hp_embed star star := by
    intro t
    simp only [hp_embed, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      QuadraticAlgebra.lift_apply_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      zero_mul, add_zero]
    simp [Rat.smul_def]
  apply hg4_embedMatrix_injective
  change ((hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x).map hp_embed = (1 : Matrix _ _ hp_K).map hp_embed
  rw [Matrix.mul_one, Matrix.map_mul, Matrix.conjTranspose_map _ hstar, hg4_sigmaK_map,
    Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)

/-! ## Chain checks -/

/-- Chain check: under product one and for a Hermitian invariant `H`, the cup form on `H¹_σ` is
skew-Hermitian. From `hg4_shapiroH1_bijective`, `hg4_cupH1_shapiro`, `pc_SPar_mk` and
`pc_S_skew`. -/
example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (hHerm : Hᴴ = H)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) (u v : hg_eqH1 σ g) :
    hg4_cupH1 σ g H u v + star (hg4_cupH1 σ g H v u) = 0 := by
  have hprodT : (List.ofFn (pc_tuple σ g)).prod = 1 := by
    have : List.ofFn (pc_tuple σ g) = (List.ofFn g).map σ := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, hprod, map_one]
  obtain ⟨x, rfl⟩ := (hg4_shapiroH1_bijective σ g hprod).2 u
  obtain ⟨y, rfl⟩ := (hg4_shapiroH1_bijective σ g hprod).2 v
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hg4_cupH1_shapiro σ g hprod H hHerm hinv, hg4_cupH1_shapiro σ g hprod H hHerm hinv,
    pc_SPar_mk _ H hprodT hHerm (fun i => hinv _) a b a.2 b.2,
    pc_SPar_mk _ H hprodT hHerm (fun i => hinv _) b a b.2 a.2, star_mul, star_natCast,
    mul_comm (star _), ← mul_add,
    pc_S_skew _ H hprodT hHerm (fun i => hinv _) a b a.2 b.2, mul_zero]

/-- Chain check toward `hpol` (the field, basis and Gram shape of `g32d_ParabolicPolarization`, with
`c = |G| > 0`): on the explicit lifted complex of the G32 root with the `K`-form `hg4_sigmaK`, the
Shapiro classes of H6's `K`-certificate form a `K`-basis of `H¹_σ`, in which `(1 + 2ζ)·hg4_cupH1`
has Gram matrix `|G|·g32H0 ζ`. From `hg4_sigmaK_tuple`, `hg4_shapiroH1_bijective`,
`hg4_cupH1_shapiro`, `pc_SPar_mk` and H6 (`hp_certK_mem`, `hp_certK_independent`,
`hp_vparK_finrank`, `hp_certK_gram`). Transporting the basis to the Prym lattice of a fibre is the
geometric part of H4 and stage H5. -/
example : ∃ c : {c : ℚ // 0 < c}, ∃ e : Module.Basis (Fin 6) hp_K (hg_eqH1 hg4_sigmaK b4b_root),
    (∀ a, e a = hg4_shapiroH1 hg4_sigmaK b4b_root (Submodule.Quotient.mk
      ⟨hp_certK a, hg4_sigmaK_tuple ▸ hp_certK_mem a⟩)) ∧
    LinearMap.toMatrix₂ e e ((1 + 2 * pc_zeta) • hg4_cupH1 hg4_sigmaK b4b_root 1) =
      ((c : ℚ) : hp_K) • HodgeLean.Papers.g32H0 pc_zeta := by
  have hstar : Function.Semiconj hp_embed star star := by
    intro t
    simp only [hp_embed, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      QuadraticAlgebra.lift_apply_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      zero_mul, add_zero]
    simp [Rat.smul_def]
  have hinv : ∀ x, (hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x = 1 := fun x => by
    apply hg4_embedMatrix_injective
    change ((hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x).map hp_embed = (1 : Matrix _ _ hp_K).map hp_embed
    rw [Matrix.mul_one, Matrix.map_mul, Matrix.conjTranspose_map _ hstar, hg4_sigmaK_map,
      Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  have hprod := b63d_root_product
  have hprodT : (List.ofFn (pc_tuple hg4_sigmaK b4b_root)).prod = 1 := by
    have : List.ofFn (pc_tuple hg4_sigmaK b4b_root) = (List.ofFn b4b_root).map hg4_sigmaK := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, hprod, map_one]
  have hmem : ∀ a, hp_certK a ∈ pc_Z (pc_tuple hg4_sigmaK b4b_root) := fun a =>
    hg4_sigmaK_tuple ▸ hp_certK_mem a
  have hind : ∀ c : Fin 6 → hp_K,
      ∑ a, c a • hp_certK a ∈ pc_trivialPart (pc_tuple hg4_sigmaK b4b_root) → c = 0 := by
    rw [hg4_sigmaK_tuple]
    exact hp_certK_independent
  have hdim : Module.finrank hp_K (pc_Vpar (pc_tuple hg4_sigmaK b4b_root)) = 6 := by
    rw [hg4_sigmaK_tuple]
    exact hp_vparK_finrank
  have hgram : ∀ a b, (1 + 2 * pc_zeta) *
      pc_S (pc_tuple hg4_sigmaK b4b_root) 1 (hp_certK a) (hp_certK b) =
        HodgeLean.Papers.g32H0 pc_zeta a b := by
    rw [hg4_sigmaK_tuple]
    exact hp_certK_gram
  let Φ := LinearEquiv.ofBijective (hg4_shapiroH1 hg4_sigmaK b4b_root)
    (hg4_shapiroH1_bijective hg4_sigmaK b4b_root hprod)
  let v : Fin 6 → pc_Vpar (pc_tuple hg4_sigmaK b4b_root) :=
    fun a => Submodule.Quotient.mk ⟨hp_certK a, hmem a⟩
  have hli : LinearIndependent hp_K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine congrFun (hind c ?_)
    have hmk : (Submodule.Quotient.mk (∑ a, c a • (⟨hp_certK a, hmem a⟩ :
        pc_Z (pc_tuple hg4_sigmaK b4b_root))) : pc_Vpar (pc_tuple hg4_sigmaK b4b_root)) = 0 := by
      rw [← hc]
      change Submodule.mkQ _ (∑ a, c a • _) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hmk
    simpa using hmk
  let e₀ := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])
  have he₀ : ∀ a, e₀ a = v a := fun a => by simp [e₀]
  refine ⟨⟨(Fintype.card b4b_Group : ℚ), by exact_mod_cast Fintype.card_pos⟩, e₀.map Φ,
    fun a => by simp [he₀, Φ, v], Matrix.ext fun a b => ?_⟩
  rw [map_smul, Matrix.smul_apply, LinearMap.toMatrix₂_apply, Module.Basis.map_apply,
    Module.Basis.map_apply, he₀, he₀, Matrix.smul_apply]
  change (1 + 2 * pc_zeta) • hg4_cupH1 hg4_sigmaK b4b_root 1
      (hg4_shapiroH1 hg4_sigmaK b4b_root (v a)) (hg4_shapiroH1 hg4_sigmaK b4b_root (v b)) = _
  rw [hg4_cupH1_shapiro hg4_sigmaK b4b_root hprod 1 (by simp) hinv,
    pc_SPar_mk _ 1 hprodT (by simp) (fun i => hinv _) _ _ (hmem a) (hmem b), ← hgram a b]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- Chain check (the conjugation ambiguity): complex conjugation turns the certificate of `σ` into a
certificate of `σ̄` with the conjugate Gram matrix. For the conjugate root tuple and the conjugate
H6 parameters, `(1 + 2ω̄)·S = conj (g32H0 ω a b)`. From `hg4_pcS_map` with `f = starRingEnd ℂ` and
`hp_cert_gram`. The `K`-form `(1 + 2ζ)·S` is the same for both embeddings of `K`; which embedding
is used decides between `σ` and `σ̄` (`hg4_sigmaK_trace`). -/
example (a b : Fin 6) :
    (1 + 2 * star HodgeLean.Papers.g32h_omega) *
        pc_S (fun j => (hp_rootTuple j).map star) 1 (fun j k => star (hp_cert a j k))
          (fun j k => star (hp_cert b j k)) =
      star (HodgeLean.Papers.g32H0 HodgeLean.Papers.g32h_omega a b) := by
  have h := hg4_pcS_map (starRingEnd ℂ) (fun t => rfl) hp_rootTuple 1 (hp_cert a) (hp_cert b)
  have h1 : (1 : Matrix (Fin 4) (Fin 4) ℂ).map (starRingEnd ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1] at h
  change _ * pc_S (fun j => (hp_rootTuple j).map (starRingEnd ℂ)) 1
    (fun j k => starRingEnd ℂ (hp_cert a j k)) (fun j k => starRingEnd ℂ (hp_cert b j k)) = _
  rw [← h, ← hp_cert_gram a b, star_mul, star_add, star_one, star_mul, star_ofNat,
    starRingEnd_apply]
  ring

/-- Chain check (the decision between `σ` and `σ̄`): the character value `3 + ζ` of the `K`-form at
the first root entry goes to `3 + ω`, the character value of `σ = b4b_toMatrix`, under `hp_embed`,
and to `3 + ω̄ ≠ 3 + ω` under the conjugate embedding. From `hg4_sigmaK_trace`, `hg4_sigmaK_map`
and `hp_embed_zeta`. -/
example : hp_embed (Matrix.trace (hg4_sigmaK (b4b_root 0))) =
      Matrix.trace (b4b_toMatrix (b4b_root 0)) ∧
    Matrix.trace (b4b_toMatrix (b4b_root 0)) = 3 + HodgeLean.Papers.g32h_omega ∧
    star (hp_embed (Matrix.trace (hg4_sigmaK (b4b_root 0)))) ≠
      hp_embed (Matrix.trace (hg4_sigmaK (b4b_root 0))) := by
  have h1 : hp_embed (Matrix.trace (hg4_sigmaK (b4b_root 0))) =
      Matrix.trace (b4b_toMatrix (b4b_root 0)) := by
    rw [← hg4_sigmaK_map, Matrix.trace, Matrix.trace, map_sum]
    rfl
  have h2 : hp_embed (Matrix.trace (hg4_sigmaK (b4b_root 0))) =
      3 + HodgeLean.Papers.g32h_omega := by
    rw [hg4_sigmaK_trace, map_add, map_ofNat, hp_embed_zeta]
  refine ⟨h1, h1 ▸ h2, ?_⟩
  rw [h2]
  intro h
  have him : (HodgeLean.Papers.g32h_omega).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hq := HodgeLean.Papers.g32h_omega_sq_add
  have hre := congrArg Complex.re hq
  have him2 := congrArg Complex.im hq
  simp [pow_two, him] at hre him2
  nlinarith [sq_nonneg (HodgeLean.Papers.g32h_omega.re + 1 / 2)]

end HodgeLean.Foundations.Program
