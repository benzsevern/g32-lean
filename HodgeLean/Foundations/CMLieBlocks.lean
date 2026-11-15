import HodgeLean.Foundations.CMLieBlocksProofs

/-! # The Powers flagship, stage A2b: `Lie(G_k)_ℂ` in block form, and the power model (FROZEN SPEC)

Stage A2b of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103), the second stage of the plan's algebra track
(`docs/roadmap/pw-flagship-plan.md`, §3.1 item 1 and §4.2 row A2b). Each theorem is proved by the
matching `_aux` theorem in `CMLieBlocksProofs.lean`. The definitions are in
`CMLieBlocksDefs.lean`.

Setting: a finite-dimensional `ℚ`-space `V`, a CM field `L` with complex conjugation `c`, a
`ℚ`-algebra map `ι : L →ₐ[ℚ] Module.End ℚ V`, `u ∈ L` with `u² = -d`, `d > 0` (so `k = ℚ(u)`), and a
bilinear form `E` with `E(ι(a) x, y) = E(x, ι(c a) y)`, nondegenerate, alternating where stated.
`W_τ = cmEigenspace ι τ` are A2a's joint eigenspaces, the blocks are indexed by the embeddings `v`
with `v(u) = i√d` (`cmPlusEmb L u d`), and `X_τ = cmBlock ι τ X` is the diagonal block of an
endomorphism `X` of `ℂ ⊗ V`. It claims:

* the complexification of PW-0's `gkLie E ι(L) ι(u)` is cut out over `ℂ` by the same equations
  (S1); for `X` commuting with `ι(L)_ℂ`, `X_τ` is the restriction of `X` to `W_τ` (S2), and taking
  blocks is multiplicative (S3), hence a Lie map on such `X`;
* the contragredient action: for such `X` that are also `E`-skew, the pairing `W_τ̄ → W_τ^∨` of A2a
  carries `X_τ̄` to `-X_τᵀ` (S4); so `tr X_τ̄ = -tr X_τ` (S5) and
  `tr (ι(u)_ℂ X) = 2 i√d Σ_v tr X_v` (S6, general `d`);
* the block form: `X ↦ (X_v)_v` maps `complexSpan (gkLie …)` into
  `{(X_v) ∈ ⊕_v 𝔤𝔩(W_v) : Σ_v tr X_v = 0}` (S7), injectively (S8) and onto (S9, for alternating
  `E`), and so `dim_ℂ = e m² - 1` (S10, for `V ≠ 0`); the trace condition is on the sum, not per
  block;
* the power model `ℂ ⊗ (V ⊗ ℚ^r) ≃ ⊕_v (W_v ⊗ ℂ^r) × (W_v^∨ ⊗ ℂ^r)`, sending `W_v ⊗ w` and `W_v̄ ⊗ w`
  to the `v`-th summand and intertwining the action of such `X` with `multiplicityLie` of `X_v` on
  each summand (S11);
* specialization and degenerate checks: at `L = k`, `u² = -3` (one block), the complexified
  `gkLie` is `WeilPower.complexSU` (S12); for `V = 0` the dimension formula of S10 fails (S13); the
  per-block condition `tr X_v = 0` is false as soon as there are two blocks (S14); the binders
  `E`, nondegeneracy, alternation and the Rosati condition are met by an explicit form on `L × L`
  for every CM field (S15).

It does not claim: any Hodge-theoretic statement, or that the Hodge Lie algebra equals `gkLie`
(that is PW-0's binder `HodgeLieIsGk`); invariants of the power model (stages A3a, A3b, A4); the
Weil classes `⊗_v det W^v` (stage A5); anything about an actual abelian variety or its powers;
group-level statements about `G_k(A)`. The results are implications from the stated binders. HC
no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

section General

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- **S1, the complexified `gkLie`.** `gkLie E ι(L) ι(u)` is cut out by rational linear equations,
so its complexification is cut out by the same equations over `ℂ`: commuting with every
`ι(a)_ℂ`, `E_ℂ`-skew, `tr X = 0` and `tr (ι(u)_ℂ X) = 0`.
Source: Bourbaki, *Algèbre*, ch. II, §5 (extension of scalars commutes with kernels); PW v0.3,
Subsection 2.3 (`G_k(A) = Lef(A) ∩ SL_k(V)`); the case `R = ℚ[J]` is
`spec_eqw_mem_complexSpan_weilSU_iff` (`Foundations/EQWCore.lean`). -/
theorem spec_a2b_mem_complexSpan_gkLie_iff [FiniteDimensional ℚ V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule ↔
      (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) ∧
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) X = 0 ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) ((ι u).baseChange ℂ * X) = 0 :=
  spec_a2b_mem_complexSpan_gkLie_iff_aux ι E u X

example [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (u : L) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule) (a : L) :
    X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X :=
  ((spec_a2b_mem_complexSpan_gkLie_iff ι E u X).mp hX).1 a

end General

section NumberField

variable {L : Type*} [Field L] [NumberField L] [FiniteDimensional ℚ V]

/-- **S2, blocks are restrictions.** If `X` commutes with every `ι(a)_ℂ`, it preserves each `W_τ`,
and its block `X_τ` is the restriction of `X` to `W_τ`.
Source: PW v0.3, Subsection 2.3 (`Lef(A)` commutes with `L`, so `Lef(A)_ℂ` preserves each
`W_v`); Bourbaki, *Algèbre*, Ch. VII, §5 (an endomorphism commuting with a family preserves its
joint eigenspaces). -/
theorem spec_a2b_cmBlock_apply (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (x : cmEigenspace ι τ) :
    ((cmBlock ι τ X x : cmEigenspace ι τ) : ℂ ⊗[ℚ] V) = X x :=
  spec_a2b_cmBlock_apply_aux ι τ X hX x

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) (x : cmEigenspace ι τ) :
    X x ∈ cmEigenspace ι τ := by
  rw [← spec_a2b_cmBlock_apply ι τ X hX x]
  exact (cmBlock ι τ X x).2

/-- **S3, blocks are multiplicative.** If `Y` commutes with every `ι(a)_ℂ`, then
`(X Y)_τ = X_τ Y_τ`. So on the endomorphisms commuting with `ι(L)_ℂ`, in particular on
`complexSpan (gkLie …)` (S1), `X ↦ X_τ` is a Lie map.
Source: PW v0.3, Subsection 2.3 (`Lef(A)_ℂ = ∏_v GL(W_v)`, the components being restrictions). -/
theorem spec_a2b_cmBlock_mul (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hY : ∀ a : L, Y * (ι a).baseChange ℂ = (ι a).baseChange ℂ * Y) :
    cmBlock ι τ (X * Y) = cmBlock ι τ X * cmBlock ι τ Y :=
  spec_a2b_cmBlock_mul_aux ι τ X Y hY

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) (X Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hY : ∀ a : L, Y * (ι a).baseChange ℂ = (ι a).baseChange ℂ * Y) :
    cmBlock ι τ (X * Y - Y * X) =
      cmBlock ι τ X * cmBlock ι τ Y - cmBlock ι τ Y * cmBlock ι τ X := by
  rw [map_sub, spec_a2b_cmBlock_mul ι τ X Y hY, spec_a2b_cmBlock_mul ι τ Y X hX]

/-- **S4, the contragredient action.** If `X` commutes with every `ι(a)_ℂ` and is `E_ℂ`-skew,
then A2a's pairing `W_τ̄ → W_τ^∨`, `y ↦ E_ℂ(·, y)`, carries the block `X_τ̄` to the contragredient
`-X_τᵀ` of the block `X_τ`. With A2a's S10 (the pairing is bijective for a CM field and a
nondegenerate Rosati-compatible `E`) this is the statement that `X` acts on `W_τ̄ ≅ W_τ^∨`
contragrediently.
Source: PW v0.3, Subsection 2.3 ("The polarization identifies `W̄_v` with `W_v^∨`; after
complexification `Lef(A)_ℂ = ∏_v GL(W_v)`, acting on `W̄_v` contragrediently"); the case `L = k`,
`d = 3` is `WeilPower.complexSU_contragredient` (`Foundations/WeilPowerLie.lean`). -/
theorem spec_a2b_contragredient (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
        (cmEigenspace ι (cmConjEmbedding τ)) ∘ₗ cmBlock ι (cmConjEmbedding τ) X =
      SchurWeyl.dualLie ℂ (cmEigenspace ι τ) (cmBlock ι τ X) ∘ₗ
        WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
          (cmEigenspace ι (cmConjEmbedding τ)) :=
  spec_a2b_contragredient_aux ι E τ X hX hs

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y))
    (y : cmEigenspace ι (cmConjEmbedding τ)) :
    WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
        (cmEigenspace ι (cmConjEmbedding τ)) (cmBlock ι (cmConjEmbedding τ) X y) =
      SchurWeyl.dualLie ℂ (cmEigenspace ι τ) (cmBlock ι τ X)
        (WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
          (cmEigenspace ι (cmConjEmbedding τ)) y) :=
  LinearMap.congr_fun (spec_a2b_contragredient ι E τ X hX hs) y

/-- **S13, degenerate check `m = 0`.** For `V = 0` the complexified `gkLie` is zero. So the
dimension formula of S10, `(dim + 1) · 2[L : ℚ] = (dim V)²`, fails at `V = 0` (the `example`):
S10 needs `V ≠ 0`, that is `m ≥ 1`.
Source: constructed here; compare PW v0.3, Subsection 2.3 (`G_k(A)_ℂ = {(g_v) : ∏ det g_v = 1}`,
of dimension `e m² - 1` for `m ≥ 1`). -/
theorem spec_a2b_finrank_complexSpan_gkLie_of_subsingleton [Subsingleton V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L) :
    Module.finrank ℂ (complexSpan (gkLie E ι.range (ι u)).toSubmodule) = 0 :=
  spec_a2b_finrank_complexSpan_gkLie_of_subsingleton_aux ι E u

example [Subsingleton V] (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L) :
    (Module.finrank ℂ (complexSpan (gkLie E ι.range (ι u)).toSubmodule) + 1) *
        (2 * Module.finrank ℚ L) ≠ Module.finrank ℚ V ^ 2 := by
  rw [spec_a2b_finrank_complexSpan_gkLie_of_subsingleton ι E u,
    Module.finrank_zero_of_subsingleton (R := ℚ) (M := V)]
  have := Module.finrank_pos (R := ℚ) (M := L)
  omega

variable [IsCMField L]

/-- **S5, traces of conjugate blocks.** For a CM field `L`, a nondegenerate form `E` with
`E(ι(a) x, y) = E(x, ι(c a) y)`, and `X` commuting with `ι(L)_ℂ` and `E_ℂ`-skew,
`tr X_τ̄ = -tr X_τ`.
Source: PW v0.3, Subsection 2.3 (`W̄_v ≅ W_v^∨`, acted on contragrediently); S4 and A2a's
`spec_a2a_duality_bijective` (the trace of `-Xᵀ` is `-tr X`). -/
theorem spec_a2b_trace_cmBlock_conj (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ _ (cmBlock ι (cmConjEmbedding τ) X) =
      -LinearMap.trace ℂ _ (cmBlock ι τ X) :=
  spec_a2b_trace_cmBlock_conj_aux ι E hE hRos τ X hX hs

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ _ (cmBlock ι τ X) +
      LinearMap.trace ℂ _ (cmBlock ι (cmConjEmbedding τ) X) = 0 := by
  rw [spec_a2b_trace_cmBlock_conj ι E hE hRos τ X hX hs, add_neg_cancel]

/-- **S6, the `k`-trace in blocks, general `d`.** Under the hypotheses of S5 and `u² = -d`,
`d > 0`: `tr (ι(u)_ℂ X) = 2 i√d · Σ_v tr X_v`, the sum over the embeddings `v` with `v(u) = i√d`.
So the condition `tr (J X) = 0` of `gkLie` is `Σ_v tr X_v = 0`, a condition on the sum over the
`k`-part, and `i√d` is `omegaC d` (at `d = 3`, `WeilPower.root`; see `CMLieBlocksDefs.lean`).
Source: PW v0.3, Subsection 2.3 (`G_k(A) = {g : N_{L/k}(det_L g) = 1}`, and over `ℂ`
`G_k(A)_ℂ = {(g_v) : ∏_v det g_v = 1}`); `ι(u)_ℂ = τ(u) = ±i√d` on `W_τ`, and S5. -/
theorem spec_a2b_trace_J (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ (ℂ ⊗[ℚ] V) ((ι u).baseChange ℂ * X) =
      2 * HodgeBlocks.WeilAction.omegaC d *
        ∑ v : cmPlusEmb L u d, LinearMap.trace ℂ _ (cmBlock ι v.1 X) :=
  spec_a2b_trace_J_aux ι E hE hRos u hd hu X hX hs

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) (hu : u ^ 2 = algebraMap ℚ L (-3)) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ (ℂ ⊗[ℚ] V) ((ι u).baseChange ℂ * X) =
      2 * HodgeBlocks.WeilAction.omegaC 3 *
        ∑ v : cmPlusEmb L u 3, LinearMap.trace ℂ _ (cmBlock ι v.1 X) :=
  spec_a2b_trace_J ι E hE hRos u (by norm_num) hu X hX hs

/-- **S7, block form: into the trace-sum-zero algebra.** For `X` in the complexified `gkLie`, the
blocks `(X_v)_v`, `v(u) = i√d`, satisfy `Σ_v tr X_v = 0`.
Source: PW v0.3, Subsection 2.3 (`G_k(A)_ℂ = {(g_v) : ∏_v det g_v = 1}`); S1 and S6. -/
theorem spec_a2b_cmBlock_mem_traceZero (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule) :
    (fun v : cmPlusEmb L u d => cmBlock ι v.1 X) ∈ cmBlockTraceZero ι u d :=
  spec_a2b_cmBlock_mem_traceZero_aux ι E hE hRos u hd hu X hX

/-- **S8, block form: injectivity.** Two elements of the complexified `gkLie` with the same blocks
`X_v` at every `v` with `v(u) = i√d` are equal: the blocks at `v̄` are then equal by S4 and A2a's
duality, and `ℂ ⊗ V = ⊕_τ W_τ` with every `τ` of the form `v` or `v̄`.
Source: PW v0.3, Subsection 2.3 (`Lef(A)_ℂ = ∏_v GL(W_v)`: an element is determined by its
components on the `W_v`). -/
theorem spec_a2b_eq_of_cmBlock_eq (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule)
    (hY : Y ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule)
    (h : ∀ v : cmPlusEmb L u d, cmBlock ι v.1 X = cmBlock ι v.1 Y) :
    X = Y :=
  spec_a2b_eq_of_cmBlock_eq_aux ι E hE hRos u hd hu X Y hX hY h

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule)
    (h : ∀ v : cmPlusEmb L u d, cmBlock ι v.1 X = 0) :
    X = 0 :=
  spec_a2b_eq_of_cmBlock_eq ι E hE hRos u hd hu X 0 hX (Submodule.zero_mem _)
    (fun v => (h v).trans (map_zero _).symm)

/-- **S9, block form: surjectivity.** For an alternating `E`, every tuple `(Y_v)_v` with
`Σ_v tr Y_v = 0` is the tuple of blocks of an element of the complexified `gkLie`: the one acting
by `Y_v` on `W_v` and contragrediently on `W_v̄`. With S3, S7 and S8 this is the Lie isomorphism
`Lie(G_k(A))_ℂ ≅ {(X_v) ∈ ⊕_v 𝔤𝔩(W_v) : Σ_v tr X_v = 0}` (the `example`: a bijection).
Source: PW v0.3, Subsection 2.3 (`G_k(A)_ℂ = {(g_v) : ∏_v det g_v = 1}`); the case `L = k`,
`d = 3` is `WeilPower.complexSUEquiv` (`Foundations/WeilPowerLie.lean`). -/
theorem spec_a2b_exists_of_mem_traceZero (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (Y : ∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1))
    (hY : Y ∈ cmBlockTraceZero ι u d) :
    ∃ X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule,
      ∀ v : cmPlusEmb L u d, cmBlock ι v.1 X = Y v :=
  spec_a2b_exists_of_mem_traceZero_aux ι E hE hAlt hRos u hd hu Y hY

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    Set.BijOn (fun X (v : cmPlusEmb L u d) => cmBlock ι v.1 X)
      (complexSpan (gkLie E ι.range (ι u)).toSubmodule) (cmBlockTraceZero ι u d) := by
  refine ⟨fun X hX => spec_a2b_cmBlock_mem_traceZero ι E hE hRos u hd hu X hX,
    fun X hX Y hY h => spec_a2b_eq_of_cmBlock_eq ι E hE hRos u hd hu X Y hX hY
      (fun v => congrFun h v), fun Y hY => ?_⟩
  obtain ⟨X, hX, h⟩ := spec_a2b_exists_of_mem_traceZero ι E hE hAlt hRos u hd hu Y hY
  exact ⟨X, hX, funext h⟩

/-- **S10, dimension.** For `V ≠ 0` and an alternating `E`, the complexified `gkLie` has dimension
`e m² - 1`, with `e = [L : ℚ] / 2` blocks of dimension `m = dim V / [L : ℚ]`; in a form without
division, `(dim + 1) · 2[L : ℚ] = (dim V)²`. At `L = k` this is `dim 𝔰𝔩_n = n² - 1`
(`dim V = 2n`); at `m = 1` it is `e - 1`, the torus of PW v0.3, proof of Corollary 5.13.
Source: PW v0.3, Subsection 2.3 (`G_k(A)_ℂ = {(g_v) : ∏_v det g_v = 1}`, `dim W_v = m`) and
the proof of Corollary 5.13 (`m = 1`: a torus of dimension `e - 1`); S7–S9 and A2a's
`spec_a2a_finrank`, `spec_a2a_card_plus`. -/
theorem spec_a2b_finrank_complexSpan_gkLie [Nontrivial V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    (Module.finrank ℂ (complexSpan (gkLie E ι.range (ι u)).toSubmodule) + 1) *
        (2 * Module.finrank ℚ L) =
      Module.finrank ℚ V ^ 2 :=
  spec_a2b_finrank_complexSpan_gkLie_aux ι E hE hAlt hRos u hd hu

example [Nontrivial V] (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (hm : Module.finrank ℚ V = Module.finrank ℚ L) :
    (Module.finrank ℂ (complexSpan (gkLie E ι.range (ι u)).toSubmodule) + 1) * 2 =
      Module.finrank ℚ L := by
  have h := spec_a2b_finrank_complexSpan_gkLie ι E hE hAlt hRos u hd hu
  rw [hm, sq, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

/-- **S14, falsification: the trace condition is not per block.** With two or more blocks
(`[L : ℚ] ≥ 4`, `e ≥ 2`) and `V ≠ 0`, some element of the complexified `gkLie` has a block of
nonzero trace. So `Lie(G_k(A))_ℂ` is not `⊕_v 𝔰𝔩(W_v)`; the condition `Σ_v tr X_v = 0` of S7 and
S9 cannot be strengthened to `tr X_v = 0` for each `v`.
Source: PW v0.3, Subsection 2.3 (`G_k(A)` is an extension of the torus `{(t_v) : ∏_v t_v = 1}`,
of dimension `e - 1 > 0`, by `∏_v SL(W_v)`). -/
theorem spec_a2b_exists_trace_cmBlock_ne_zero [Nontrivial V]
    (hL : 4 ≤ Module.finrank ℚ L) (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    ∃ X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule,
      ∃ v : cmPlusEmb L u d, LinearMap.trace ℂ _ (cmBlock ι v.1 X) ≠ 0 :=
  spec_a2b_exists_trace_cmBlock_ne_zero_aux hL ι E hE hAlt hRos u hd hu

example [Nontrivial V] (hL : 4 ≤ Module.finrank ℚ L) (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    ¬ ∀ X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule,
      ∀ v : cmPlusEmb L u d, LinearMap.trace ℂ _ (cmBlock ι v.1 X) = 0 := by
  intro hall
  obtain ⟨X, hX, v, hv⟩ :=
    spec_a2b_exists_trace_cmBlock_ne_zero hL ι E hE hAlt hRos u hd hu
  exact hv (hall X hX v)

open Classical in
/-- **S11, the power model.** For every `r`, there is a `ℂ`-linear isomorphism
`ℂ ⊗ (V ⊗ ℚ^r) ≃ ⊕_v (W_v ⊗ ℂ^r) × (W_v^∨ ⊗ ℂ^r)`, over the embeddings `v` with `v(u) = i√d`, that
sends `x ⊗ w` (`x ∈ W_v`) to `(x ⊗ w, 0)` in the `v`-th summand, sends `y ⊗ w` (`y ∈ W_v̄`) to
`(0, E_ℂ(·, y) ⊗ w)` there, and intertwines the action of every `X` commuting with `ι(L)_ℂ` and
`E_ℂ`-skew (on `V ⊗ ℚ^r`, trivially on `ℚ^r`) with `multiplicityLie` of the block `X_v` on the
`v`-th summand.
Source: PW v0.3, proof of Theorem 4.2, first paragraph
(`H¹(A^r, ℂ) = ⊕_v ((W^v ⊗ U) ⊕ ((W^v)^∨ ⊗ U))`, `U = ℂ^r`); the case `L = k`, `d = 3` is
`WeilPower.powerModel` with `WeilPower.powerModel_intertwines`
(`Foundations/WeilPowerTransport.lean`). -/
theorem spec_a2b_powerModel (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) (r : ℕ) :
    ∃ e : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        (∀ v : cmPlusEmb L u d,
          InvariantsExterior.Space ℂ (cmEigenspace ι v.1) (Fin r → ℂ) (Fin r → ℂ)),
      (∀ (v : cmPlusEmb L u d) (x : cmEigenspace ι v.1) (w : Fin r → ℂ),
        e ((WeilPower.powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
          Pi.single v (x ⊗ₜ[ℂ] w, 0)) ∧
      (∀ (v : cmPlusEmb L u d) (y : cmEigenspace ι (cmConjEmbedding v.1)) (w : Fin r → ℂ),
        e ((WeilPower.powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
          Pi.single v (0, WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι v.1)
            (cmEigenspace ι (cmConjEmbedding v.1)) y ⊗ₜ[ℂ] w)) ∧
      (∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
        (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) →
        (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) →
        ∀ z (v : cmPlusEmb L u d), e (WeilPower.powerAction r X z) v =
          InvariantsExterior.multiplicityLie ℂ (cmEigenspace ι v.1) (Fin r → ℂ) (Fin r → ℂ)
            (cmBlock ι v.1 X) (e z v)) :=
  spec_a2b_powerModel_aux ι E hE hRos u hd hu r

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) (r : ℕ) :
    Nonempty ((ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
      (∀ v : cmPlusEmb L u d,
        InvariantsExterior.Space ℂ (cmEigenspace ι v.1) (Fin r → ℂ) (Fin r → ℂ))) :=
  let ⟨e, _⟩ := spec_a2b_powerModel ι E hE hRos u hd hu r
  ⟨e⟩

variable (L) in
/-- **S15, the binders can be met.** For every CM field `L`, the form
`((x₁, x₂), (y₁, y₂)) ↦ Tr(x₁ c(y₂)) - Tr(x₂ c(y₁))` on `V = L × L` with the diagonal action is
nondegenerate, alternating, and satisfies the Rosati condition `E(a x, y) = E(x, c(a) y)`. So the
binders `hE`, `hAlt`, `hRos` of S5–S11 and S14 are jointly satisfiable, with `V ≠ 0`.
Source: constructed here; compare Shimura, *Abelian varieties with complex multiplication and
modular functions*, §4–6; `Algebra.traceForm_nondegenerate` (Mathlib) and
`IsCMField.complexConj` (an involution, preserving the trace). -/
theorem spec_a2b_cmSymplectic_binders :
    (a2b_cmSymplectic L).Nondegenerate ∧ (a2b_cmSymplectic L).IsAlt ∧
      ∀ (a : L) (x y : L × L),
        a2b_cmSymplectic L (a2a_diagAction L a x) y =
          a2b_cmSymplectic L x (a2a_diagAction L (IsCMField.complexConj L a) y) :=
  spec_a2b_cmSymplectic_binders_aux

example (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    (Module.finrank ℂ (complexSpan (gkLie (a2b_cmSymplectic L) (a2a_diagAction L).range
        (a2a_diagAction L u)).toSubmodule) + 1) * (2 * Module.finrank ℚ L) =
      Module.finrank ℚ (L × L) ^ 2 :=
  spec_a2b_finrank_complexSpan_gkLie (a2a_diagAction L) (a2b_cmSymplectic L)
    (spec_a2b_cmSymplectic_binders L).1 (spec_a2b_cmSymplectic_binders L).2.1
    (spec_a2b_cmSymplectic_binders L).2.2 u hd hu

end NumberField

section QuadraticSpecialization

variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ V]

/-- **S12, specialization `L = k` (one block).** If `[L : ℚ] = 2` and `u² = -3`, then `L = ℚ(u)`,
`ι(L) = ℚ[ι(u)]`, and the complexified `gkLie E ι(L) ι(u)` is `WeilPower.complexSU`, the `d = 3`
single-block algebra `≅ 𝔰𝔩(W)` of `Foundations/WeilPowerLie.lean`. The hypotheses `hJ` and
`hskew` are those of `complexSU` (`hJ` follows from `hu`; `hskew` from a Rosati condition with
`c(u) = -u`).
Source: PW v0.3, proof of Theorem 3.1, first paragraph (`e = 1`, `L = k`, `G_k(A) = SU(V, H)`);
`spec_pw0_gkLie_adjoin_eq` (`Adapters/PowersVocabulary.lean`) and
`spec_eqw_complexSpan_weilSU_eq_complexSU` (`Foundations/EQWCore.lean`). -/
theorem spec_a2b_complexSpan_gkLie_eq_complexSU (hL : Module.finrank ℚ L = 2)
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt) (u : L) (hu : u ^ 2 = algebraMap ℚ L (-3))
    (hJ : (ι u).comp (ι u) = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (ι u x) y = -E x (ι u y)) :
    complexSpan (gkLie E ι.range (ι u)).toSubmodule =
      (WeilPower.complexSU E hE (ι u) hJ hskew).toSubmodule :=
  spec_a2b_complexSpan_gkLie_eq_complexSU_aux hL ι E hE hAlt u hu hJ hskew

example (hL : Module.finrank ℚ L = 2) (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt) (u : L)
    (hu : u ^ 2 = algebraMap ℚ L (-3)) (hJ : (ι u).comp (ι u) = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (ι u x) y = -E x (ι u y))
    (X : WeilPower.complexSU E hE (ι u) hJ hskew) :
    X.1 ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule := by
  rw [spec_a2b_complexSpan_gkLie_eq_complexSU hL ι E hE hAlt u hu hJ hskew]
  exact X.2

end QuadraticSpecialization

end HodgeLean.Foundations
