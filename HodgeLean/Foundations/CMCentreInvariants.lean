import HodgeLean.Foundations.CMCentreInvariantsProofs

/-! # The Powers flagship, stage A4: the centre (Lemma 4.1(b), (c), T4) (FROZEN SPEC)

Stage A4 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103), in the plan's algebra track (`docs/roadmap/pw-flagship-plan.md`,
§4.2 row A4, step T4, Lemma 4.1(b), (c)). Each theorem is proved by the matching `_aux` theorem in
`CMCentreInvariantsProofs.lean`. The definitions `CountedGeneratorProduct`,
`MultiCountedProduct`, `constWeightDegree`, `blockTheta`, `multiDetW`, `multiDetWDual` and
`centreNormalProducts` are in `CMCentreInvariantsDefs.lean`. Everything is pure linear algebra.

Setting: A3b's blocks `v : Fin e`, `Space_v = (W_v ⊗ U_v) × (W_v^∨ ⊗ U'_v)`,
`MultiSpace = Π_v Space_v`, with `f = (f_v) ∈ Π_v 𝔤𝔩(W_v)` acting on `⋀^k MultiSpace` by
`exteriorDer k (piMap (multiplicityLie ∘ f))`. The model's `W v` plays the paper's `W^v`.

**Convention for the centre.** A2b (`cmBlockTraceZero`) gives `Lie(G_k)_ℂ` as the tuples
`(X_v) ∈ ⊕_v 𝔤𝔩(W_v)` with `Σ_v tr X_v = 0`, on the homology blocks `W_v`. On `W^v = W_v^∨` the
tuple acts by `f_v = -X_vᵀ`, and `Σ_v tr f_v = -Σ_v tr X_v`, so in the model `Lie(G_k)` is again
`{f : Σ_v tr f_v = 0}` (S5). Its centre is the torus `{(t_v · id) : Σ_v t_v · dim W_v = 0}` (S4);
with all `dim W_v = m > 0` this is `Σ_v t_v = 0`, the Lie algebra of the paper's
`{(d_v) : ∏_v d_v = 1}`. A monomial with `α_v` factors `det(W_v ⊗ a)` and `β_v` factors
`det(W_v^∨ ⊗ a')` in block `v` has weight `c_v = α_v - β_v`, and `f` acts on it by the scalar
`Σ_v c_v · tr f_v` (S2); the paper's character `∏_v det_v^{-c_v}` of `∏_v GL(W_v)` is the same
weight read through the contragredient. The torus kills it exactly when `c_v = c` is constant
(S4), which needs every `W_v ≠ 0`.

**Normalization of `θ` and `det`.** `theta` is basis-free (the image of the identity tensor);
`detW` and `detWDual` use `Module.finBasis` and its dual basis, so each changes by a scalar with
the basis, but their product does not. S6 fixes the scalar:
`θ(a, a')^m = (-1)^{m(m-1)/2} · m! · det(W ⊗ a) ∧ det(W^∨ ⊗ a')`, `m = dim W`.

It claims:

* **weights** (S1, one block; S2, all blocks): the eigenvalue identities above;
* **the bridge** (S3): A3b's `multiGeneratedDegree k` is the span of the counted products;
* **Lie(torus)-invariants** (S4): inside `multiGeneratedDegree k`, the joint kernel of the torus
  is `constWeightDegree k`, the span of the monomials with constant `c_v`;
* **`Lie(G_k)`-invariants** (S5): the joint kernel of `{f : Σ_v tr f_v = 0}` is
  `constWeightDegree k` (with A3b's S1);
* **the `θ` identity** (S6), over any field;
* **Lemma 4.1(c), one block** (S7, S8): the weight-`c` monomials span the same space as the
  products of contractions with `c` factors `det(W ⊗ a)` (or `|c|` factors `det(W^∨ ⊗ a')`), and
  this is the `det^c`-isotypic part of the `𝔰𝔩(W)`-invariants;
* **T4, all blocks** (S9): `constWeightDegree k`, in the exterior algebra, is the degree-`k` part
  of the span of the paper's normal forms `∏ Θ_v · ∏_{j<c} ∏_v det(W^v ⊗ x_{j,v})` and their duals;
* **degenerate and falsification checks**: `e = 1` (S10: the torus condition is vacuous), a
  monomial of weight `(1, 0)` that is not invariant (S11), and characteristic `2`, where
  `θ^2 = 0` but `det(W ⊗ 1) ∧ det(W^∨ ⊗ 1) ≠ 0` (S12: the `m!` matters). `c = 0` and `m = 1`, `2`
  are `example`s after S8 and S6.

It does not claim: any statement about the groups `G_k`, `GL(W_v)`, `SL(W_v)` or their tori (only
Lie algebras); the identification of the model with `H^*(A^r, ℂ)` or of `constWeightDegree` with
Hodge classes (stage A6); the Weil classes or their descent (stage A5); blocks indexed by an
arbitrary `Fintype` (only `Fin e`); positive characteristic, except the falsification S12. The
results are unconditional linear algebra; the flagship uses them in an implication from
`HodgeLieIsGk`. HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup
open scoped TensorProduct
namespace HodgeLean.Foundations
open InvariantsExterior SchurWeyl Module

section AnyField

variable {K : Type*} [Field K]
variable {W U U' : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']

/-- **S6, the `θ` identity.** With `m = dim W`, in the exterior algebra of
`Space = (W ⊗ U) × (W^∨ ⊗ U')`, over any field:
`θ(a, a')^m = (-1)^{m(m-1)/2} · m! · det(W ⊗ a) ∧ det(W^∨ ⊗ a')`. Writing
`θ = Σ_i x_i y_i` with `x_i = w_i ⊗ a`, `y_i = w_i^∨ ⊗ a'`, the even elements `x_i y_i` commute
and square to `0`, so `θ^m = m! · x_1 y_1 ⋯ x_m y_m`, and moving every `y_i` to the right past the
`x_j`, `j > i`, costs `m(m-1)/2` transpositions. Both sides are basis-free.
Source: PW v0.3, Lemma 4.1(c) (`det(W ⊗ x) det(W^∨ ⊗ x')` is `GL(W)`-invariant, hence a
polynomial in contractions), made explicit; plan `docs/roadmap/pw-flagship-plan.md`, §3.1
item 3 (`θ(x, x')^m = ± m! det(W ⊗ x) ∧ det(W^∨ ⊗ x')`, replacing the `GL` first fundamental
theorem); Bourbaki, *Algèbre*, ch. III, §7 (graded commutativity). -/
theorem spec_a4_theta_pow (a : U) (a' : U') :
    ((theta (K := K) (W := W) a a' : ExteriorAlgebra K (Space K W U U'))) ^ finrank K W =
      ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) * ((finrank K W).factorial : K)) •
        ((detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) *
          (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U'))) :=
  spec_a4_theta_pow_aux a a'

/-- S6 at `m = 1`: the sign is `+` and `1! = 1`, so `θ(a, a') = det(W ⊗ a) ∧ det(W^∨ ⊗ a')`. -/
example (h : finrank K W = 1) (a : U) (a' : U') :
    ((theta (K := K) (W := W) a a' : ExteriorAlgebra K (Space K W U U'))) =
      (detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) *
        (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U')) := by
  have hs := spec_a4_theta_pow (K := K) (W := W) a a'
  have h1 : ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) *
      ((finrank K W).factorial : K)) = 1 := by
    rw [h]; simp
  rw [h1, one_smul] at hs
  rw [← hs]
  conv_rhs => rw [h, pow_one]

/-- S6 at `m = 2`: `θ(a, a')^2 = -2 · det(W ⊗ a) ∧ det(W^∨ ⊗ a')`. -/
example (h : finrank K W = 2) (a : U) (a' : U') :
    ((theta (K := K) (W := W) a a' : ExteriorAlgebra K (Space K W U U'))) ^ 2 =
      (-2 : K) • ((detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) *
        (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U'))) := by
  have hs := spec_a4_theta_pow (K := K) (W := W) a a'
  have h2 : ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) *
      ((finrank K W).factorial : K)) = -2 := by
    rw [h]; norm_num [Nat.factorial]
  rw [h2] at hs
  rw [← hs, h]

end AnyField

/-- **S12, falsification: characteristic `0` is needed.** Over `ZMod 2`, with `W = (ZMod 2)^2` and
`U = U' = ZMod 2`: `θ(1, 1)^2 = 0` (S6 with `2! = 0`), while `det(W ⊗ 1) ∧ det(W^∨ ⊗ 1) ≠ 0`. With
one-dimensional `U`, `U'`, every contraction is a multiple of `θ(1, 1)`, so in degree `4` the
product of the two determinants is not a polynomial in contractions: S6 cannot be divided by
`m!`, and Lemma 4.1(c) (S7) fails in characteristic `2`.
Source: constructed here; PW v0.3, Lemma 4.1 (stated over `ℂ`); the polarization identity in the
proof of Lemma 4.1(a) divides by `m!`. -/
theorem spec_a4_theta_sq_charTwo :
    ((theta (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (U' := ZMod 2) 1 1 :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2)))) ^ 2 = 0 ∧
      (detW (K := ZMod 2) (W := Fin 2 → ZMod 2) (U' := ZMod 2) (1 : ZMod 2) :
          ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2))) *
        (detWDual (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (1 : ZMod 2) :
          ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2))) ≠ 0 :=
  spec_a4_theta_sq_charTwo_aux

example : ¬ ∃ r : ZMod 2,
    (detW (K := ZMod 2) (W := Fin 2 → ZMod 2) (U' := ZMod 2) (1 : ZMod 2) :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2))) *
      (detWDual (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (1 : ZMod 2) :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2))) =
      r • ((theta (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (U' := ZMod 2) 1 1 :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2)))) ^ 2 := by
  rintro ⟨r, hr⟩
  obtain ⟨h0, hne⟩ := spec_a4_theta_sq_charTwo
  rw [h0, smul_zero] at hr
  exact hne hr

variable {K : Type*} [Field K] [CharZero K]

section OneBlock

variable {W U U' : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']

/-- **S1, weights, one block (Lemma 4.1(b), Lie form).** A product with `α` factors
`det(W ⊗ a)` and `β` factors `det(W^∨ ⊗ a')` (and any contractions) is an eigenvector of every
`f ∈ 𝔤𝔩(W)`, with eigenvalue `(α - β) · tr f`: the derivative of `det^{α-β}`.
Source: PW v0.3, Lemma 4.1(b) ("`GL(W)` acts on a product with `α` factors `det(W ⊗ x)` and `β`
factors `det(W^∨ ⊗ x')` by `det^{α-β}`"), in Lie form; the generators' eigenvalues are
`InvariantsExterior.lie_theta`, `lie_detW`, `lie_detWDual`, and products follow from
`exteriorDer_wedge` (Leibniz). -/
theorem spec_a4_exteriorDer_counted {k α β : ℕ} {g : ⋀[K]^k (Space K W U U')}
    (hg : CountedGeneratorProduct k α β g) (f : Module.End K W) :
    exteriorDer k (multiplicityLie K W U U' f) g =
      (((α : K) - β) * LinearMap.trace K W f) • g :=
  spec_a4_exteriorDer_counted_aux hg f

example (f : Module.End K W) (a : U) :
    exteriorDer (finrank K W) (multiplicityLie K W U U' f) (detW a) =
      LinearMap.trace K W f • detW a := by
  rw [spec_a4_exteriorDer_counted (CountedGeneratorProduct.detW a) f]
  simp

/-- **S7, Lemma 4.1(c), normal form.** For `c : ℤ`, the products of weight `α - β = c` span the
same space as those with `α = 0` or `β = 0`, that is, contractions times `c` factors
`det(W ⊗ a)` if `c ≥ 0`, or `|c|` factors `det(W^∨ ⊗ a')` if `c < 0`. Each pair
`det(W ⊗ a) ∧ det(W^∨ ⊗ a')` is, up to sign, `θ(a, a')^m / m!` (S6).
Source: PW v0.3, Lemma 4.1(c) and its proof (each `det(W ⊗ x) det(W^∨ ⊗ x')` is
`GL(W)`-invariant, hence by (b) a polynomial in contractions); S6 replaces the `GL` first
fundamental theorem. -/
theorem spec_a4_counted_span_normal (k : ℕ) (c : ℤ) :
    Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ CountedGeneratorProduct k α β g} =
      Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ (α = 0 ∨ β = 0) ∧ CountedGeneratorProduct k α β g} :=
  spec_a4_counted_span_normal_aux k c

example (k : ℕ) (c : ℤ) {α β : ℕ} (hc : (α : ℤ) - β = c) {g : ⋀[K]^k (Space K W U U')}
    (hg : CountedGeneratorProduct k α β g) :
    g ∈ Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ (α = 0 ∨ β = 0) ∧ CountedGeneratorProduct k α β g} := by
  rw [← spec_a4_counted_span_normal k c]
  exact Submodule.subset_span ⟨α, β, hc, hg⟩

/-- **S8, Lemma 4.1(c), the `det^c`-isotypic part.** For `W ≠ 0` and `c : ℤ`, the elements of
`generatedDegree k` (the `𝔰𝔩(W)`-invariants, by `invariants_eq_generatedDegree` when `U`, `U'`
are finite-dimensional) on which every `f ∈ 𝔤𝔩(W)` acts by `c · tr f` are the span of the
contractions times `c` factors `det(W ⊗ a)`, or `|c|` factors `det(W^∨ ⊗ a')` when `c < 0`.
Source: PW v0.3, Lemma 4.1(c) ("for `c ≥ 0`, the `det^c`-isotypic part of `Λ(W)^{SL(W)}` is
spanned by products of contractions and `c` factors `det(W ⊗ x)`; likewise for `c < 0`"), in
Lie form; from S1, S7, and the separation of the weights by `f = id` (eigenvalue
`(α - β) · dim W`). -/
theorem spec_a4_isotypic_eq_span [Nontrivial W] (k : ℕ) (c : ℤ) :
    generatedDegree (K := K) (W := W) (U := U) (U' := U') k ⊓
        (⨅ f : Module.End K W, LinearMap.ker (exteriorDer k (multiplicityLie K W U U' f) -
          ((c : K) * LinearMap.trace K W f) • LinearMap.id)) =
      Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ (α = 0 ∨ β = 0) ∧ CountedGeneratorProduct k α β g} :=
  spec_a4_isotypic_eq_span_aux k c

/-- S8 at `c = 0` (Lemma 4.1(b), second assertion, Lie form): the `𝔤𝔩(W)`-invariants inside
`generatedDegree k` are the span of the pure products of contractions. -/
example [Nontrivial W] (k : ℕ) :
    generatedDegree (K := K) (W := W) (U := U) (U' := U') k ⊓
        (⨅ f : Module.End K W, LinearMap.ker (exteriorDer k (multiplicityLie K W U U' f))) =
      Submodule.span K {g : ⋀[K]^k (Space K W U U') | CountedGeneratorProduct k 0 0 g} := by
  have h := spec_a4_isotypic_eq_span (K := K) (W := W) (U := U) (U' := U') k 0
  simp only [Int.cast_zero, zero_mul, zero_smul] at h
  have h0 : ∀ f : Module.End K W, exteriorDer k (multiplicityLie K W U U' f) - 0 =
      exteriorDer k (multiplicityLie K W U U' f) := fun f => LinearMap.ext fun x => by simp
  simp only [h0] at h
  rw [h]
  congr 1
  ext g
  constructor
  · rintro ⟨α, β, hc, hαβ, hg⟩
    obtain ⟨rfl, rfl⟩ : α = 0 ∧ β = 0 := by omega
    exact hg
  · intro hg
    exact ⟨0, 0, rfl, Or.inl rfl, hg⟩

end OneBlock

section Main

variable {e : ℕ} {W U U' : Fin e → Type*}
  [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
  [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
  [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]

/-- **S2, weights, all blocks.** A monomial with `α_v` factors `det(W_v ⊗ a)` and `β_v` factors
`det(W_v^∨ ⊗ a')` in block `v` is an eigenvector of every `f ∈ Π_v 𝔤𝔩(W_v)`, with eigenvalue
`Σ_v (α_v - β_v) · tr f_v`. For the block scalars `f_v = t_v · id` this is
`Σ_v c_v · t_v · dim W_v` (the `example`).
Source: PW v0.3, proof of Theorem 4.2, "Derived group" step ("each such `P` is an eigenvector of
`∏_v GL(W_v)`, with character `∏_v det_v^{-c_v}`, where `c_v = α_v - β_v`"), in Lie form on
`W^v`; S1 per block, `exteriorDer_map` for `ι_v`, `exteriorDer_wedge` for products. -/
theorem spec_a4_exteriorDer_multiCounted {k : ℕ} {α β : Fin e → ℕ}
    {x : ⋀[K]^k (MultiSpace K W U U')} (hx : MultiCountedProduct k α β x)
    (f : (v : Fin e) → Module.End K (W v)) :
    exteriorDer k (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)) x =
      (∑ v, ((α v : K) - β v) * LinearMap.trace K (W v) (f v)) • x :=
  spec_a4_exteriorDer_multiCounted_aux hx f

example {k : ℕ} {α β : Fin e → ℕ} {x : ⋀[K]^k (MultiSpace K W U U')}
    (hx : MultiCountedProduct k α β x) (t : Fin e → K) :
    exteriorDer k (LinearMap.piMap fun v =>
        multiplicityLie K (W v) (U v) (U' v) (t v • LinearMap.id)) x =
      (∑ v, ((α v : K) - β v) * (t v * finrank K (W v))) • x := by
  rw [spec_a4_exteriorDer_multiCounted hx]
  simp [LinearMap.trace_id]

/-- **S3, the bridge to A3b.** `multiGeneratedDegree k` is the span of the counted products: every
`MultiGeneratorProduct` carries some determinant counts `α`, `β`.
Source: constructed here; A3b's `MultiGeneratorProduct` and `CountedGeneratorProduct` have the
same constructors, the latter recording the counts of PW v0.3, Lemma 4.1(b). -/
theorem spec_a4_multiGeneratedDegree_eq_span_counted (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k =
      Submodule.span K {x | ∃ α β : Fin e → ℕ, MultiCountedProduct k α β x} :=
  spec_a4_multiGeneratedDegree_eq_span_counted_aux k

example {k : ℕ} {α β : Fin e → ℕ} {x : ⋀[K]^k (MultiSpace K W U U')}
    (hx : MultiCountedProduct k α β x) :
    x ∈ multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k := by
  rw [spec_a4_multiGeneratedDegree_eq_span_counted k]
  exact Submodule.subset_span ⟨α, β, hx⟩

/-- **S4, Lie(torus)-invariants.** Let every `W_v` be nonzero. Inside A3b's
`multiGeneratedDegree k`, the joint kernel of the block scalars `(t_v · id)_v` with
`Σ_v t_v · dim W_v = 0` (the centre of `{f : Σ_v tr f_v = 0}`) is `constWeightDegree k`, the span
of the monomials with constant weight `c_v = c`. By S2 such a scalar acts on a monomial by
`Σ_v c_v t_v dim W_v`, which vanishes on the whole torus exactly when `c_v` is constant.
Source: PW v0.3, proof of Theorem 4.2, "Centre" step ("the character `∏_v d_v^{-c_v}` is trivial
on `{(d_v) : ∏_v d_v = 1}` if and only if `c_v = c` is the same for all `v`. Since the `P` are
eigenvectors spanning the `G_k(A)^der_ℂ`-invariants, the `G_k(A)_ℂ`-invariants are spanned by
those `P` with constant `c_v = c`"), in Lie form; A2b's `cmBlockTraceZero` for the trace
condition. -/
theorem spec_a4_torus_invariants [∀ v, Nontrivial (W v)] (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k ⊓
        (⨅ t : {t : Fin e → K // ∑ v, t v * (finrank K (W v) : K) = 0},
          LinearMap.ker (exteriorDer k (LinearMap.piMap fun v =>
            multiplicityLie K (W v) (U v) (U' v) (t.1 v • LinearMap.id)))) =
      constWeightDegree (K := K) (W := W) (U := U) (U' := U') k :=
  spec_a4_torus_invariants_aux k

example [∀ v, Nontrivial (W v)] (k : ℕ) :
    constWeightDegree (K := K) (W := W) (U := U) (U' := U') k ≤
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k := by
  rw [← spec_a4_torus_invariants k]
  exact inf_le_left

/-- **S5, the `Lie(G_k)`-invariants.** Let every `W_v` be nonzero and `U_v`, `U'_v`
finite-dimensional. The joint kernel on `⋀^k (Π_v Space_v)` of the tuples `f ∈ Π_v 𝔤𝔩(W_v)` with
`Σ_v tr f_v = 0` (the model's `Lie(G_k)_ℂ`, A2b's trace condition read on `W^v`) is
`constWeightDegree k`. It combines A3b's S1 (the `⊕_v 𝔰𝔩(W_v)`-invariants) with S4 (the centre),
since `f = (f_v - (tr f_v / dim W_v) · id) + (tr f_v / dim W_v) · id`.
Source: PW v0.3, proof of Theorem 4.2, "Derived group" and "Centre" steps; A2b's
`spec_a2b_cmBlock_mem_traceZero` and `spec_a2b_exists_of_mem_traceZero`
(`Lie(G_k)_ℂ ≅ {(X_v) : Σ_v tr X_v = 0}`); A3b's
`spec_a3b_invariants_eq_multiGeneratedDegree`. -/
theorem spec_a4_traceZero_invariants [∀ v, FiniteDimensional K (U v)]
    [∀ v, FiniteDimensional K (U' v)] [∀ v, Nontrivial (W v)] (k : ℕ) :
    (⨅ f : {f : (v : Fin e) → Module.End K (W v) // ∑ v, LinearMap.trace K (W v) (f v) = 0},
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f.1 v)))) =
      constWeightDegree (K := K) (W := W) (U := U) (U' := U') k :=
  spec_a4_traceZero_invariants_aux k

/-- With S5: an element of `constWeightDegree k` is killed by every `(f_v) ∈ ⊕_v 𝔰𝔩(W_v)`. -/
example [∀ v, FiniteDimensional K (U v)] [∀ v, FiniteDimensional K (U' v)]
    [∀ v, Nontrivial (W v)] (k : ℕ) (x : ⋀[K]^k (MultiSpace K W U U'))
    (hx : x ∈ constWeightDegree (K := K) (W := W) (U := U) (U' := U') k)
    (f : (v : Fin e) → slEnd K (W v)) :
    exteriorDer k (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)) x = 0 := by
  rw [← spec_a4_traceZero_invariants k] at hx
  have h := (Submodule.mem_iInf _).mp hx ⟨fun v => (f v : Module.End K (W v)), by
    simp [(mem_slEnd.mp (f _).property)]⟩
  exact h

/-- **S9, T4: the normal form for all blocks.** Included in the exterior algebra of
`Π_v Space_v`, `constWeightDegree k` is the degree-`k` part of the span of the paper's normal
forms: products of contractions `Θ_v(a, a')` times `c` factors `∏_v det(W_v ⊗ x_{j,v})`, or times
`c` factors `∏_v det(W_v^∨ ⊗ x'_{j,v})`, `c : ℕ`. Block by block S7 brings a constant-weight
monomial to contractions times `c` (or `|c|` dual) determinants of that block, and regrouping the
determinants of all blocks by `j` changes only a sign.
Source: PW v0.3, proof of Theorem 4.2, "Centre" step ("If `c ≥ 0`, Lemma 4.1(c), applied block by
block, writes such a `P` as a polynomial in the contractions times a product of `c` tensors
`⊗_v det(W^v ⊗ x_v)`; if `c < 0`, the same holds with `det((W^v)^∨ ⊗ x'_v)`"); Bourbaki,
*Algèbre*, ch. III, §7, no. 7, Proposition 10 (the exterior algebra of a direct sum as the skew
tensor product). -/
theorem spec_a4_constWeightDegree_eq_normal (k : ℕ) :
    Submodule.map (⋀[K]^k (MultiSpace K W U U')).subtype
        (constWeightDegree (K := K) (W := W) (U := U) (U' := U') k) =
      ⋀[K]^k (MultiSpace K W U U') ⊓
        Submodule.span K (centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) :=
  spec_a4_constWeightDegree_eq_normal_aux k

/-- With S5 and S9 (the shape A6 uses): a degree-`k` invariant of `{f : Σ_v tr f_v = 0}` lies in
the span of the normal forms. -/
example [∀ v, FiniteDimensional K (U v)] [∀ v, FiniteDimensional K (U' v)]
    [∀ v, Nontrivial (W v)] (k : ℕ) (x : ⋀[K]^k (MultiSpace K W U U'))
    (hx : x ∈ ⨅ f : {f : (v : Fin e) → Module.End K (W v) //
        ∑ v, LinearMap.trace K (W v) (f v) = 0},
      LinearMap.ker (exteriorDer k
        (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f.1 v)))) :
    (x : ExteriorAlgebra K (MultiSpace K W U U')) ∈
      Submodule.span K (centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) := by
  rw [spec_a4_traceZero_invariants k] at hx
  have h := Submodule.mem_map_of_mem (f := (⋀[K]^k (MultiSpace K W U U')).subtype) hx
  rw [spec_a4_constWeightDegree_eq_normal k] at h
  exact h.2

end Main

section Degenerate

/-- **S10, degenerate check `e = 1`.** With one block every weight vector is constant, so
`constWeightDegree k = multiGeneratedDegree k`: the torus condition is vacuous, and with S5 the
`Lie(G_k)`-invariants are A3b's (the `example`), as at `e = 1`, where `G_k = SU`.
Source: constructed here; plan `docs/roadmap/pw-flagship-plan.md`, §2 ("At `e = 1`, `G_k = SU`, so
the torus is trivial and T4 is vacuous"); A3b's `spec_a3b_multiGeneratedDegree_fin_one`. -/
theorem spec_a4_constWeightDegree_fin_one {W U U' : Fin 1 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] (k : ℕ) :
    constWeightDegree (K := K) (W := W) (U := U) (U' := U') k =
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k :=
  spec_a4_constWeightDegree_fin_one_aux k

example {W U U' : Fin 1 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, Nontrivial (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)] [∀ v, FiniteDimensional K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] [∀ v, FiniteDimensional K (U' v)]
    (k : ℕ) :
    (⨅ f : {f : (v : Fin 1) → Module.End K (W v) // ∑ v, LinearMap.trace K (W v) (f v) = 0},
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f.1 v)))) =
      (⨅ f : (v : Fin 1) → slEnd K (W v),
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)))) := by
  rw [spec_a4_traceZero_invariants k, spec_a4_constWeightDegree_fin_one k,
    spec_a3b_invariants_eq_multiGeneratedDegree k]

/-- **S11, falsification: a monomial of non-constant weight is not invariant.** Take two blocks
with `W_v = U_v = U'_v = K` and `x = ι_0 (det(W_0 ⊗ 1))`, of weight `(c_0, c_1) = (1, 0)`. Then
`x` is `⊕_v 𝔰𝔩(W_v)`-invariant (it lies in `multiGeneratedDegree`), but not
`Lie(G_k)`-invariant: `f = (id, -id)` has `Σ_v tr f_v = 0` and acts on `x` by `1`. With S5, `x`
is not in `constWeightDegree` (the `example`).
Source: constructed here; PW v0.3, proof of Theorem 4.2, "Centre" step (the character
`∏_v d_v^{-c_v}` is nontrivial on `{∏_v d_v = 1}` unless `c_v` is constant). -/
theorem spec_a4_nonconstant_not_invariant :
    (exteriorPower.map (finrank K K) (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :
          ⋀[K]^(finrank K K) (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K))) ∈
      multiGeneratedDegree (K := K) (W := fun _ : Fin 2 => K) (U := fun _ => K) (U' := fun _ => K)
        (finrank K K) ∧
    (exteriorPower.map (finrank K K) (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :
          ⋀[K]^(finrank K K) (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K))) ∉
      (⨅ f : {f : (v : Fin 2) → Module.End K K // ∑ v, LinearMap.trace K K (f v) = 0},
        LinearMap.ker (exteriorDer (finrank K K)
          (LinearMap.piMap fun v => multiplicityLie K K K K (f.1 v)))) :=
  spec_a4_nonconstant_not_invariant_aux

example :
    (exteriorPower.map (finrank K K) (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :
          ⋀[K]^(finrank K K) (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K))) ∉
      constWeightDegree (K := K) (W := fun _ : Fin 2 => K) (U := fun _ => K) (U' := fun _ => K)
        (finrank K K) := by
  rw [← spec_a4_traceZero_invariants (finrank K K)]
  exact (spec_a4_nonconstant_not_invariant (K := K)).2

end Degenerate

end HodgeLean.Foundations
