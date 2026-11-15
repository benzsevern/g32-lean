import HodgeLean.Foundations.CMWeilClassesProofs

/-! # The Powers flagship, stage A5: Weil classes for a general CM field (FROZEN SPEC)

Stage A5 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103), step T6 ("Weil classes") of the plan
(`docs/roadmap/pw-flagship-plan.md`, §3.1 item 4 and §4.2 row A5). Each theorem is proved by the
matching `_aux` theorem in `CMWeilClassesProofs.lean`. The definitions are in
`CMWeilClassesDefs.lean`.

Setting: a finite-dimensional `ℚ`-space `V`, standing for `H¹(A, ℚ)` as in the model
`⋀(V ⊗ ℚ^r)` of `H^*(A^r, ℚ)`; a `ℚ`-algebra map `ι : L →ₐ[ℚ] Module.End ℚ V`; `u ∈ L` with
`u² = -d`, `d > 0`. `W_τ = cmEigenspace ι τ` are A2a's joint eigenspaces (the paper's `W^v` for
`τ = σ_v`), the plus embeddings `v(u) = i√d` are `cmPlusEmb L u d`, and
`V₊ = cmPlusPart ι u d = ⊕_v W_v`. The pullback along `f_a : A^r → A`, `a ∈ L^r`, is PW-0's
`cmPowerPullback ι.range (a5_cmCoeff ι a)`. It claims:

* the top power of a direct sum: for bases `b_v` of the `W_v`, `⋀^n V₊` (as a subspace of
  `⋀^n (ℂ ⊗ V)`) is the line spanned by the nonzero wedge of the concatenated bases,
  `⊗_v det W^v` (S1);
* the pullback: `f_a` sends `x ∈ W_τ` to `x ⊗ (τ(a_i))_i` (S2), so it sends `∧_j x_j`, with
  `x_j ∈ W_{κ(j)}`, to `∧_j (x_j ⊗ κ(j)(a))`, the paper's
  `f_a^*(⊗_v det W^v) = ⊗_v det(W^v ⊗ σ_v(a))` (S3);
* `ρ` is surjective: the vectors `(τ(a_i))_{τ, i}`, `a ∈ L^r`, span all of `ℂ^{Hom(L, ℂ) × r}`,
  for a number field `L` (S4);
* descent: every `∧_j (x_j ⊗ y_{κ(j)})`, `y` arbitrary, lies in the `ℂ`-span of the
  `∧_j (x_j ⊗ κ(j)(a))`, `a ∈ L^r` (S5);
* the contractions `Θ_τ(x, x')` lie in the complexified rational Hodge classes of degree `2` of
  the model, as an implication from PW-0's binder `HodgeLieIsGk` (S6);
* identification with the Weil plane of PW-0: for a Weil action `A` with `A.J = ι(u)`, the
  complexification of `A.weilClasses` is the sum of the two lines `⊗_v det W^v` and
  `⊗_v det W^v̄` (S7), for every number field `L`, in particular at `L = k`;
* degenerate checks and falsifications: for `V = 0` the top power vanishes in positive degree, so
  S1's binders cannot be met there (S8); for `r = 0` the model vanishes in positive degree (S9);
  with a single plus embedding `V₊ = W_v` (S10); on the conjugate block the pullback by `u` is
  `-i√d`, not `i√d` (S11); rational coefficients `a ∈ ℚ^r` do not give a surjective `ρ` once
  there are two embeddings (S12), and their pullbacks do not span the class S5 reaches (S13).

It does not claim: that the pulled-back Weil classes are Hodge classes, or any generation
statement for the Hodge classes of the model (stages A4, A6); anything about the actual
cohomology of `A^r`, the morphisms `f_a`, or the order `𝒪 = L ∩ End(A)` (G-track; the spans here
run over `a ∈ L^r`); that the contractions are combinations of divisor classes (that needs the
Lefschetz `(1,1)` theorem on `A^r`). The results are implications from the stated binders. HC no
distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

section General

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- **S1, the top power of a direct sum.** Let `b_v` be bases of the blocks `W_v`, `v(u) = i√d`,
all of size `m`, and `σ : Fin n ≃ {v} × Fin m` an enumeration. The image of `⋀^n V₊` in
`⋀^n (ℂ ⊗ V)`, `V₊ = ⊕_v W_v`, is the line spanned by the wedge of the concatenated bases, and that
wedge is nonzero: `⋀^n V₊ = ⊗_v ⋀^m W_v` is a line, compatibly with the block decomposition.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes"
(`⋀^n(⊕_v W^v) = ⊗_v det W^v`, `n = e m`); Bourbaki, *Algèbre*, Ch. III, §7, no. 7 (the top
exterior power of an `n`-dimensional space is a line, spanned by the wedge of a basis); A2a's
`spec_a2a_iSupIndep` (the blocks are independent). -/
theorem spec_a5_range_exteriorPower_cmPlusPart (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    {m n : ℕ} (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (σ : Fin n ≃ cmPlusEmb L u d × Fin m) :
    LinearMap.range (exteriorPower.map n (cmPlusPart ι u d).subtype) =
        ℂ ∙ exteriorPower.ιMulti ℂ n
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V)) ∧
      exteriorPower.ιMulti ℂ n
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V)) ≠ 0 :=
  spec_a5_range_exteriorPower_cmPlusPart_aux ι u d b σ

example (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {m n : ℕ}
    (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (σ : Fin n ≃ cmPlusEmb L u d × Fin m) :
    LinearMap.range (exteriorPower.map n (cmPlusPart ι u d).subtype) ≠ ⊥ := by
  obtain ⟨h, h0⟩ := spec_a5_range_exteriorPower_cmPlusPart ι u d b σ
  rw [h]
  exact fun hb => h0 (Submodule.span_singleton_eq_bot.mp hb)

/-- **S2, the pullback in degree one.** For `a ∈ L^r` and `x ∈ W_τ`, the complexified pullback
along `f_a`, `x ↦ Σ_i a_i x ⊗ e_i`, sends `x` to `x ⊗ (τ(a_1), …, τ(a_r))`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" ("the pullback `f_a^*` maps
`η ∈ W^v` to `(σ_v(a_1)η, …, σ_v(a_r)η) ∈ W^v ⊗ U`"); `cmPowerPullback`
(`Foundations/PowersVocabularyDefs.lean`). -/
theorem spec_a5_cmPowerPullback_baseChange (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    {r : ℕ} (a : Fin r → L) (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) :
    (cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ x =
      (WeilPower.powerBaseChange (V := V) r).symm (x ⊗ₜ[ℂ] (fun i => τ (a i))) :=
  spec_a5_cmPowerPullback_baseChange_aux ι τ a x hx

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) {r : ℕ} (a : Fin r → L)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) :
    WeilPower.powerBaseChange (V := V) r
        ((cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ x) =
      x ⊗ₜ[ℂ] (fun i => τ (a i)) := by
  rw [spec_a5_cmPowerPullback_baseChange ι τ a x hx, LinearEquiv.apply_symm_apply]

/-- **S3, the pullback of the determinant lines.** If `x_j ∈ W_{κ(j)}` for each `j`, the pullback
along `f_a` sends `x_1 ∧ ⋯ ∧ x_n` to `(x_1 ⊗ κ(1)(a)) ∧ ⋯ ∧ (x_n ⊗ κ(n)(a))`. For `x` the
concatenated bases of the `W_v` (`κ(j)` the block of `x_j`) this is
`f_a^*(⊗_v det W^v) = ⊗_v det(W^v ⊗ σ_v(a))`; for the bases of the `W_v̄` it is the conjugate
part.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes", display
`f_a^*(⊗_v det W^v) = ⊗_v det(W^v ⊗ σ_v(a))`; S2. -/
theorem spec_a5_map_cmPowerPullback_ιMulti (ι : L →ₐ[ℚ] Module.End ℚ V) {r n : ℕ}
    (κ : Fin n → (L →ₐ[ℚ] ℂ)) (x : Fin n → ℂ ⊗[ℚ] V) (hx : ∀ j, x j ∈ cmEigenspace ι (κ j))
    (a : Fin r → L) :
    exteriorPower.map n ((cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ)
        (exteriorPower.ιMulti ℂ n x) =
      a5_cmDet r x (fun j i => κ j (a i)) :=
  spec_a5_map_cmPowerPullback_ιMulti_aux ι κ x hx a

example (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {r m n : ℕ}
    (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (σ : Fin n ≃ cmPlusEmb L u d × Fin m) (a : Fin r → L) :
    exteriorPower.map n ((cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ)
        (exteriorPower.ιMulti ℂ n
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V))) =
      a5_cmDet r (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V))
        (fun j i => (σ j).1.1 (a i)) :=
  spec_a5_map_cmPowerPullback_ιMulti ι (fun j => (σ j).1.1) _ (fun j => (b (σ j).1 (σ j).2).2) a

/-- **S6, the contractions are complexified Hodge classes of degree `2`.** Assume PW-0's binder
`HodgeLieIsGk` (the Lie-algebra form of `Hg(A) = G_k(A)`). Let `b` be a basis of `W_τ` and `c` a
basis of `W_τ̄` dual to it under `E_ℂ`. Then the contraction
`Θ_τ(x, x') = Σ_i (b_i ⊗ x) ∧ (c_i ⊗ x')` lies in the complex span of the rational Hodge classes of
degree `2` of the model: every element of `complexSpan (gkLie …)` acts on `W_τ̄ ≅ W_τ^∨`
contragrediently (A2b's S4), so kills `Θ_τ`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Divisor classes" ("Each contraction
`Θ_v(x, x')` is invariant under `∏_w GL(W_w) ⊇ G_k(A)_ℂ` and lies in `H²(A^r, ℂ)`. By (H1) the
`G_k(A)_ℂ`-invariants in `H²(A^r, ℂ)` are the complexification of the space of rational Hodge
classes"); `WeilPower.mem_exteriorHodgeClasses_iff` (`Foundations/WeilPowerClasses.lean`). -/
theorem spec_a5_cmTheta_mem_exteriorHodgeClasses
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (hGk : HodgeLieIsGk H hH E ι.range (ι u)) (τ : L →ₐ[ℚ] ℂ) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (cmEigenspace ι τ))
    (c : Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding τ)))
    (hbc : ∀ i j, E.baseChange ℂ (b i) (c j) = if i = j then 1 else 0)
    (r : ℕ) (x x' : Fin r → ℂ) :
    a5_cmTheta r (fun i => (b i : ℂ ⊗[ℚ] V)) (fun i => (c i : ℂ ⊗[ℚ] V)) x x' ∈
      WeilPower.exteriorHodgeClasses H hH r 2 :=
  spec_a5_cmTheta_mem_exteriorHodgeClasses_aux H hH ι E u hGk τ b c hbc r x x'

example (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (hGk : HodgeLieIsGk H hH E ι.range (ι u)) (τ : L →ₐ[ℚ] ℂ) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (cmEigenspace ι τ))
    (c : Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding τ)))
    (hbc : ∀ i j, E.baseChange ℂ (b i) (c j) = if i = j then 1 else 0)
    (r : ℕ) (x x' : Fin r → ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    InvariantsExterior.exteriorDer 2 (WeilPower.powerAction r X)
      (a5_cmTheta r (fun i => (b i : ℂ ⊗[ℚ] V)) (fun i => (c i : ℂ ⊗[ℚ] V)) x x') = 0 :=
  (WeilPower.mem_exteriorHodgeClasses_iff H hH r 2 _).mp
    (spec_a5_cmTheta_mem_exteriorHodgeClasses H hH ι E u hGk τ b c hbc r x x') X hX

/-- **S8, degenerate check `V = 0`.** For `V = 0` the top power `⋀^n V₊` vanishes in every positive
degree. So the conclusion "a nonzero line" of S1 forces `n = 0`: for `V = 0` and `n > 0` the
binders of S1 (bases `b_v` and an enumeration `σ : Fin n ≃ {v} × Fin m`) cannot be met (the
`example`).
Source: constructed here; Bourbaki, *Algèbre*, Ch. III, §7 (`⋀^n 0 = 0` for `n > 0`). -/
theorem spec_a5_range_exteriorPower_cmPlusPart_subsingleton [Subsingleton V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {n : ℕ} (hn : 0 < n) :
    LinearMap.range (exteriorPower.map n (cmPlusPart ι u d).subtype) = ⊥ :=
  spec_a5_range_exteriorPower_cmPlusPart_subsingleton_aux ι u d hn

example [Subsingleton V] (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {m n : ℕ} (hn : 0 < n)
    (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (σ : Fin n ≃ cmPlusEmb L u d × Fin m) : False := by
  obtain ⟨h, h0⟩ := spec_a5_range_exteriorPower_cmPlusPart ι u d b σ
  rw [spec_a5_range_exteriorPower_cmPlusPart_subsingleton ι u d hn] at h
  exact h0 (Submodule.span_singleton_eq_bot.mp h.symm)

/-- **S10, degenerate check: a single plus embedding (`e = 1`).** If `v` is the only embedding
with `v(u) = i√d` (as for `L = k`), then `V₊ = W_v`, and S1 is the statement for the single
block `W = W_v` of `Foundations/WeilPower*.lean`.
Source: PW v0.3, Subsection 2.3 (`V_ℂ = ⊕_v (W_v ⊕ W̄_v)`, one summand when `e = 1`). -/
theorem spec_a5_cmPlusPart_eq_of_unique (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    (v : cmPlusEmb L u d) (hv : ∀ w : cmPlusEmb L u d, w = v) :
    cmPlusPart ι u d = cmEigenspace ι v.1 :=
  spec_a5_cmPlusPart_eq_of_unique_aux ι u d v hv

example (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) (v : cmPlusEmb L u d)
    (hv : ∀ w : cmPlusEmb L u d, w = v) (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmPlusPart ι u d) (a : L) :
    (ι a).baseChange ℂ x = v.1 a • x := by
  rw [spec_a5_cmPlusPart_eq_of_unique ι u d v hv] at hx
  exact (Submodule.mem_iInf _).mp hx a |> Module.End.mem_eigenspace_iff.mp

/-- **S11, falsification: the conjugate-pair sign.** On the conjugate block `W_v̄`, the pullback
along `f_u : A → A` (`r = 1`, `a = u`) is multiplication by `v̄(u) = -i√d`, not by `v(u) = i√d`:
for `y ≠ 0` in `W_v̄` the formula of S2 with the embedding `v` in place of `v̄` is false. So the
conjugate part of the Weil classes pulls back through `σ̄_v(a)`, and the paper's "likewise for the
conjugate part" uses the conjugate embeddings.
Source: PW v0.3, Subsection 2.1 (`W̄_v` is the `σ̄_v`-eigenspace) and the proof of Theorem 4.2,
paragraph "Weil classes"; S2 with `τ = v̄`. -/
theorem spec_a5_cmPowerPullback_conj (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) {d : ℚ}
    (hd : 0 < d) (v : cmPlusEmb L u d) (y : ℂ ⊗[ℚ] V)
    (hy : y ∈ cmEigenspace ι (cmConjEmbedding v.1)) (hy0 : y ≠ 0) :
    (cmPowerPullback ι.range (a5_cmCoeff ι (fun _ : Fin 1 => u))).baseChange ℂ y =
        (WeilPower.powerBaseChange (V := V) 1).symm
          (y ⊗ₜ[ℂ] (fun _ => -HodgeBlocks.WeilAction.omegaC d)) ∧
      (cmPowerPullback ι.range (a5_cmCoeff ι (fun _ : Fin 1 => u))).baseChange ℂ y ≠
        (WeilPower.powerBaseChange (V := V) 1).symm
          (y ⊗ₜ[ℂ] (fun _ => HodgeBlocks.WeilAction.omegaC d)) :=
  spec_a5_cmPowerPullback_conj_aux ι u hd v y hy hy0

example (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) {d : ℚ} (hd : 0 < d) (v : cmPlusEmb L u d)
    (y : ℂ ⊗[ℚ] V) (hy : y ∈ cmEigenspace ι (cmConjEmbedding v.1)) (hy0 : y ≠ 0) :
    ¬ ((cmPowerPullback ι.range (a5_cmCoeff ι (fun _ : Fin 1 => u))).baseChange ℂ y =
        (WeilPower.powerBaseChange (V := V) 1).symm (y ⊗ₜ[ℂ] (fun _ => v.1 u))) := by
  rw [v.2]
  exact (spec_a5_cmPowerPullback_conj ι u hd v y hy hy0).2

/-- **S12, falsification: `ρ` is not surjective on rational coefficients.** If `L` has two
distinct embeddings and `r ≥ 1`, the vectors `(τ(a_i))_{τ, i}` for `a ∈ ℚ^r` do not span: they
are constant in `τ`. So S4 needs the full `a ∈ L^r`.
Source: constructed here; compare PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" (`ρ`
is surjective because `L ⊗_ℚ ℂ ≅ ℂ^{2e}` through all embeddings). -/
theorem spec_a5_span_rat_ne_top {r : ℕ} (hr : 0 < r) (τ₁ τ₂ : L →ₐ[ℚ] ℂ) (h : τ₁ ≠ τ₂) :
    Submodule.span ℂ (Set.range (fun q : Fin r → ℚ =>
      fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (algebraMap ℚ L (q i)))) ≠ ⊤ :=
  spec_a5_span_rat_ne_top_aux hr τ₁ τ₂ h

example (τ₁ τ₂ : L →ₐ[ℚ] ℂ) (h : τ₁ ≠ τ₂) :
    Submodule.span ℂ (Set.range (fun q : Fin 1 → ℚ =>
      fun (τ : L →ₐ[ℚ] ℂ) (i : Fin 1) => τ (algebraMap ℚ L (q i)))) ≠ ⊤ :=
  spec_a5_span_rat_ne_top Nat.one_pos τ₁ τ₂ h

end General

/-- **S9, degenerate check `r = 0`.** For `r = 0` the model `ℂ ⊗ (V ⊗ ℚ⁰)` is zero, so every class
of positive degree vanishes (the `example`: the classes of S3 and S5). Theorem 4.2 is about
`r ≥ 1`.
Source: constructed here; PW v0.3, Theorem 4.2 ("for every `r ≥ 1`"). -/
theorem spec_a5_subsingleton_exteriorPower_zero {n : ℕ} (hn : 0 < n) :
    Subsingleton (⋀[ℂ]^n (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 0 → ℚ)))) :=
  spec_a5_subsingleton_exteriorPower_zero_aux hn

example {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ ⊗[ℚ] V) (y : Fin n → Fin 0 → ℂ) :
    a5_cmDet 0 x y = 0 :=
  haveI := spec_a5_subsingleton_exteriorPower_zero (V := V) hn
  Subsingleton.elim _ _

/-- **S13, falsification: descent fails over `ℚ`.** For linearly independent `x₁, x₂ ∈ ℂ ⊗ V`,
the class `(x₁ ⊗ e₁) ∧ (x₂ ⊗ e₂)` of `⋀² (ℂ ⊗ (V ⊗ ℚ²))` is not in the `ℂ`-span of the classes
`(x₁ ⊗ q) ∧ (x₂ ⊗ q)`, `q ∈ ℚ²`, which are the classes of S5 for rational `a = q` (then
`κ(j)(a) = q` for every `j`). With `x_j ∈ W_{τ_j}`, `τ₁ ≠ τ₂`, S5 does reach it through `a ∈ L²`.
So the span over `a ∈ L^r` cannot be replaced by the span over `ℚ^r`.
Source: constructed here; compare PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" (the
argument needs `O^r`, a lattice of full rank in `L^r`, not `ℤ^r`). -/
theorem spec_a5_cmDet_not_mem_span_rat (x : Fin 2 → ℂ ⊗[ℚ] V) (hx : LinearIndependent ℂ x) :
    a5_cmDet 2 x ![Pi.single 0 1, Pi.single 1 1] ∉ Submodule.span ℂ
      (Set.range (fun q : Fin 2 → ℚ => a5_cmDet 2 x (fun _ i => (q i : ℂ)))) :=
  spec_a5_cmDet_not_mem_span_rat_aux x hx

-- S13 in use: the classes over `ℚ²` do not span everything, so the span over `ℚ^r` cannot
-- replace the span over `L^r` in the descent statement.
example (x : Fin 2 → ℂ ⊗[ℚ] V) (hx : LinearIndependent ℂ x) :
    Submodule.span ℂ (Set.range (fun q : Fin 2 → ℚ => a5_cmDet 2 x (fun _ i => (q i : ℂ)))) ≠ ⊤ :=
  fun h => spec_a5_cmDet_not_mem_span_rat x hx (by rw [h]; exact Submodule.mem_top)

section NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- **S4, `ρ` is surjective.** For a number field `L` and every `r`, the vectors
`(τ(a_i))_{τ, i} ∈ ℂ^{Hom(L, ℂ) × r}`, `a ∈ L^r`, span everything: the map
`ρ : L^r ⊗_ℚ ℂ → ∏_τ ℂ^r`, `a ⊗ z ↦ (z τ(a))_τ`, is onto. Projecting to the plus embeddings gives
the paper's `ρ : L^r ⊗ ℂ → U^e` (the `example`).
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" ("`ρ` is `ℂ`-linear and
surjective, since `L ⊗_ℚ ℂ ≅ ℂ^{2e}` through all embeddings"); Dedekind–Artin independence of
characters (Mathlib `linearIndependent_monoidHom`). -/
theorem spec_a5_span_embeddings_eq_top (r : ℕ) :
    Submodule.span ℂ (Set.range (fun a : Fin r → L =>
      fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (a i))) = ⊤ :=
  spec_a5_span_embeddings_eq_top_aux r

example (u : L) (d : ℚ) (r : ℕ) :
    Submodule.span ℂ (Set.range (fun a : Fin r → L =>
      fun (v : cmPlusEmb L u d) (i : Fin r) => v.1 (a i))) = ⊤ := by
  have h := congrArg (Submodule.map (LinearMap.funLeft ℂ (Fin r → ℂ)
    (Subtype.val : cmPlusEmb L u d → (L →ₐ[ℚ] ℂ)))) (spec_a5_span_embeddings_eq_top (L := L) r)
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr
    (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective), ← Set.range_comp] at h
  exact h

/-- **S5, descent.** For any assignment `κ` of embeddings to the factors, any `x_j ∈ ℂ ⊗ V` and
any `y : Hom(L, ℂ) → ℂ^r`, the class `∧_j (x_j ⊗ y_{κ(j)})` lies in the `ℂ`-span of the classes
`∧_j (x_j ⊗ κ(j)(a))`, `a ∈ L^r`. With S3 (and `x` the concatenated bases of the `W_v`, or of the
`W_v̄`) this says that the pullbacks `f_a^*(⊗_v det W^v)`, `a ∈ L^r`, span the span of all
`⊗_v det(W^v ⊗ x_v)`, and likewise for the conjugate part.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" ("Hence the classes
`f_a^*(⊗_v det W^v)` span the span of all `⊗_v det(W^v ⊗ x_v)`"); S4 and
`multilinear_diagonal_mem_span_rat` (`Foundations/RationalPolarization.lean`) in `ℚ`-coordinates
of `L^r`. -/
theorem spec_a5_cmDet_mem_span (r : ℕ) {n : ℕ} (κ : Fin n → (L →ₐ[ℚ] ℂ))
    (x : Fin n → ℂ ⊗[ℚ] V) (y : (L →ₐ[ℚ] ℂ) → Fin r → ℂ) :
    a5_cmDet r x (fun j => y (κ j)) ∈ Submodule.span ℂ
      (Set.range (fun a : Fin r → L => a5_cmDet r x (fun j i => κ j (a i)))) :=
  spec_a5_cmDet_mem_span_aux r κ x y

example (ι : L →ₐ[ℚ] Module.End ℚ V) (r : ℕ) {n : ℕ} (κ : Fin n → (L →ₐ[ℚ] ℂ))
    (x : Fin n → ℂ ⊗[ℚ] V) (hx : ∀ j, x j ∈ cmEigenspace ι (κ j))
    (y : (L →ₐ[ℚ] ℂ) → Fin r → ℂ) :
    a5_cmDet r x (fun j => y (κ j)) ∈ Submodule.span ℂ (Set.range (fun a : Fin r → L =>
      exteriorPower.map n ((cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ)
        (exteriorPower.ιMulti ℂ n x))) := by
  simp_rw [spec_a5_map_cmPowerPullback_ιMulti ι κ x hx]
  exact spec_a5_cmDet_mem_span r κ x y

/-- **S7, identification with PW-0's Weil plane.** Let `A` be a Weil action (`J² = -d`, `d > 0`)
on a weight-one Hodge structure of Weil type, with `A.J = ι(u)`. For bases `b_v` of the `W_v` and
`b'_v` of the `W_v̄` and an enumeration `σ : Fin (k + k) ≃ {v} × Fin m`, the complexification of
the rational Weil plane `A.weilClasses` (defined from `Vs`) is the sum of the two lines
`⊗_v det W^v` and `⊗_v det W^v̄`. So the general-`L` object of S1 is what PW-0 uses; at `L = k`
(one block, S10) it is the existing `weilClasses_baseChange_eq_topLines`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes"
(`W_k(A) ⊗ ℂ = ⊗_v det W^v ⊕ ⊗_v det (W^v)^∨`); `weilClasses_baseChange_eq_topLines`
(`Adapters/F1575WeilDescent.lean`), A2a's `spec_a2a_cmPlusPart_eq_Vs`, and S1. -/
theorem spec_a5_weilClasses_baseChange_eq (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    {m : ℕ} (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (b' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1)))
    (σ : Fin (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) ≃
      cmPlusEmb L u d × Fin m) :
    ((A.weilClasses hH hW).baseChange ℂ).map
        (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V)
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
            Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))).toLinearMap =
      (ℂ ∙ exteriorPower.ιMulti ℂ _
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V))) ⊔
        (ℂ ∙ exteriorPower.ιMulti ℂ _
          (fun j => ((b' (σ j).1 (σ j).2 : cmEigenspace ι (cmConjEmbedding (σ j).1.1)) :
            ℂ ⊗[ℚ] V))) :=
  spec_a5_weilClasses_baseChange_eq_aux ι A u hJ hH hW hd b b' σ

example (ι : L →ₐ[ℚ] Module.End ℚ V) {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}
    (A : HodgeBlocks.WeilAction M d) (u : L) (hJ : A.J = ι u) (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (hW : A.IsWeilType) (hd : 0 < d) {m : ℕ}
    (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (b' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1)))
    (σ : Fin (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) ≃
      cmPlusEmb L u d × Fin m) :
    LinearMap.range (exteriorPower.map _ A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map _ A.Vsbar.subtype) =
      (ℂ ∙ exteriorPower.ιMulti ℂ _
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V))) ⊔
        (ℂ ∙ exteriorPower.ιMulti ℂ _
          (fun j => ((b' (σ j).1 (σ j).2 : cmEigenspace ι (cmConjEmbedding (σ j).1.1)) :
            ℂ ⊗[ℚ] V))) := by
  rw [← spec_a5_weilClasses_baseChange_eq ι A u hJ hH hW hd b b' σ]
  exact (Adapters.weilClasses_baseChange_eq_topLines A hH hW hd).symm

end NumberField

end HodgeLean.Foundations
