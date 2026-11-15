import HodgeLean.Foundations.CMSplittingProofs

/-! # The Powers flagship, stage A2a: CM splitting of `ℂ ⊗ V` (FROZEN SPEC)

Stage A2a of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103), the first stage of the plan's algebra track
(`docs/roadmap/pw-flagship-plan.md`, §3.1 item 1 and §4.2 row A2a). Each theorem is proved by the
matching `_aux` theorem in `CMSplittingProofs.lean`. The definitions are in
`CMSplittingDefs.lean`.

Setting: a `ℚ`-space `V`, a `ℚ`-algebra map `ι : L →ₐ[ℚ] Module.End ℚ V`, and for each
`τ : L →ₐ[ℚ] ℂ` the joint eigenspace `W_τ = cmEigenspace ι τ ⊆ ℂ ⊗ V`. It claims:

* the `W_τ` are independent for any commutative `ℚ`-algebra `L` (S1), and span `ℂ ⊗ V` when `L` is
  a number field and `V` is finite-dimensional (S2); so `ℂ ⊗ V = ⊕_τ W_τ`;
* `dim_ℂ W_τ · [L : ℚ] = dim_ℚ V` for every `τ`, that is `dim W_τ = m = dim_L V` (S3);
* complex conjugation of `ℂ ⊗ V` maps `W_τ` onto `W_τ̄` (S4);
* for `u ∈ L` with `u² = -d`, `d > 0`, exactly half of the embeddings have `τ(u) = i√d` (S5);
  the sum of the `W_τ` with `τ(u) = ω` is the `ω`-eigenspace of `ι(u)_ℂ`, for every `ω` (S6); so
  `V₊ = cmPlusPart ι u d` is the space `Vs` of any Weil action with `J = ι(u)` (S7);
* for an `L`-compatible form, `E(ι(a) x, y) = E(x, ι(c a) y)`, `E_ℂ(W_τ, W_τ') = 0` unless
  `τ = τ' ∘ c`, for any algebra endomorphism `c` (S8); for a CM field and its complex
  conjugation, `E_ℂ(W_τ, W_τ') = 0` unless `τ' = τ̄` (S9), and for nondegenerate `E` the pairing
  `W_τ̄ → W_τ^∨`, `y ↦ E_ℂ(·, y)`, is bijective (S10);
* falsifications: the dimension statement fails for the non-faithful action of `ℚ × ℚ` on `ℚ`
  through the first factor (S11); on `L × L` with the alternating trace form, which is
  compatible with the identity and not with complex conjugation, the orthogonality fails (S12).

It does not claim: the block form of `Lie(G_k)_ℂ` or of the power model (stage A2b); the
contragredient action on `W̄_τ`; the Hodge multiplicities `(p_τ, q_τ)` or any Hodge-theoretic
statement; positivity or the signature of the Hermitian form `h₀`; anything about an actual
abelian variety. No statement uses that `E` is alternating; S8–S10 hold for any bilinear `E`
with the stated compatibility. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

section General

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- **S1, independence.** The joint eigenspaces `W_τ` of the complexified action, indexed by the
`ℚ`-algebra maps `τ : L → ℂ`, are independent, for any commutative `ℚ`-algebra `L`.
Source: PW v0.3, Subsection 2.3 (`V_ℂ = ⊕_v (W_v ⊕ W̄_v)`); Bourbaki, *Algèbre*, Ch. VII, §5,
no. 9 (eigenvectors of a commuting family for distinct characters are linearly independent). -/
theorem spec_a2a_iSupIndep (ι : L →ₐ[ℚ] Module.End ℚ V) :
    iSupIndep (cmEigenspace ι) :=
  spec_a2a_iSupIndep_aux ι

example (ι : ℚ →ₐ[ℚ] Module.End ℚ V) : iSupIndep (cmEigenspace ι) :=
  spec_a2a_iSupIndep ι

/-- **S4, conjugation.** Complex conjugation of `ℂ ⊗ V` maps `W_τ` onto `W_τ̄`: `x ∈ W_τ` if and
only if `x̄ ∈ W_τ̄`.
Source: PW v0.3, Subsection 2.1 (`q_τ = p_τ̄`, which rests on `\overline{(V_ℂ)_τ} = (V_ℂ)_τ̄`). -/
theorem spec_a2a_complexConj_mem_iff (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) :
    complexConj V x ∈ cmEigenspace ι (cmConjEmbedding τ) ↔ x ∈ cmEigenspace ι τ :=
  spec_a2a_complexConj_mem_iff_aux ι τ x

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) (x : ℂ ⊗[ℚ] V)
    (hx : x ∈ cmEigenspace ι τ) :
    complexConj V x ∈ cmEigenspace ι (cmConjEmbedding τ) :=
  (spec_a2a_complexConj_mem_iff ι τ x).mpr hx

/-- **S8, orthogonality for any compatibility.** If `E(ι(a) x, y) = E(x, ι(c a) y)` for an algebra
endomorphism `c` of `L`, then `E_ℂ(W_τ, W_τ') = 0` whenever `τ ≠ τ' ∘ c`.
Source: PW v0.3, proof of Lemma 2.1 (the identity `E(ax, y) = E(x, ā y)`) and Subsection 2.3
("The polarization identifies `W̄_v` with `W_v^∨`"); Birkenhake–Lange, *Complex Abelian
Varieties*, §5.1 (the Rosati involution is the adjoint for `E`). -/
theorem spec_a2a_orthogonal_of_rosati (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (c : L →ₐ[ℚ] L)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (c a) y))
    (τ τ' : L →ₐ[ℚ] ℂ) (h : τ ≠ τ'.comp c)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) (y : ℂ ⊗[ℚ] V) (hy : y ∈ cmEigenspace ι τ') :
    E.baseChange ℂ x y = 0 :=
  spec_a2a_orthogonal_of_rosati_aux ι E c hRos τ τ' h x hx y hy

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (c : L →ₐ[ℚ] L)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (c a) y))
    (τ τ' : L →ₐ[ℚ] ℂ) (h : τ ≠ τ'.comp c) :
    ∀ x ∈ cmEigenspace ι τ, ∀ y ∈ cmEigenspace ι τ', E.baseChange ℂ x y = 0 :=
  fun x hx y hy => spec_a2a_orthogonal_of_rosati ι E c hRos τ τ' h x hx y hy

/-- **S11, falsification: dimensions need a faithful action.** For the action of `ℚ × ℚ` on `ℚ`
through the first factor (kernel `0 × ℚ`), the dimension formula of S3 fails: one eigenspace is
all of `ℂ ⊗ ℚ`, the other is `0`, and neither has dimension `1 / 2`.
Source: constructed here; compare PW v0.3, Subsection 2.3 (`dim W_v = m`, for `L` a field). -/
theorem spec_a2a_finrank_fails_nonfaithful :
    ¬ ∀ τ : ℚ × ℚ →ₐ[ℚ] ℂ,
      Module.finrank ℂ (cmEigenspace a2a_fstAction τ) * Module.finrank ℚ (ℚ × ℚ) =
        Module.finrank ℚ ℚ :=
  spec_a2a_finrank_fails_nonfaithful_aux

example : ∃ τ : ℚ × ℚ →ₐ[ℚ] ℂ,
    Module.finrank ℂ (cmEigenspace a2a_fstAction τ) * Module.finrank ℚ (ℚ × ℚ) ≠
      Module.finrank ℚ ℚ := by
  simpa using spec_a2a_finrank_fails_nonfaithful

end General

section NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- **S2, spanning.** For a number field `L` and finite-dimensional `V`, the `W_τ` span `ℂ ⊗ V`.
With S1, `ℂ ⊗ V = ⊕_{τ : L → ℂ} W_τ`.
Source: PW v0.3, Subsection 2.3 (`V_ℂ = ⊕_v (W_v ⊕ W̄_v)`); Bourbaki, *Algèbre*, Ch. V, §8
(`ℂ ⊗_ℚ L ≅ ℂ^{Hom(L, ℂ)}` for `L/ℚ` separable). -/
theorem spec_a2a_iSup_eq_top [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V) :
    ⨆ τ : L →ₐ[ℚ] ℂ, cmEigenspace ι τ = ⊤ :=
  spec_a2a_iSup_eq_top_aux ι

open Classical in
example [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V) :
    DirectSum.IsInternal (cmEigenspace ι) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩

/-- **S3, dimensions.** For a number field `L` and finite-dimensional `V`, every `W_τ` has
dimension `m = dim_L V`: `dim_ℂ W_τ · [L : ℚ] = dim_ℚ V`.
Source: PW v0.3, Subsection 2.3 (`dim W_v = m`); `V ≅ L^m` as an `L`-space, so
`ℂ ⊗ V ≅ (ℂ ⊗ L)^m ≅ (ℂ^{Hom(L, ℂ)})^m`. -/
theorem spec_a2a_finrank [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (τ : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace ι τ) * Module.finrank ℚ L = Module.finrank ℚ V :=
  spec_a2a_finrank_aux ι τ

example [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V) (τ τ' : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace ι τ) = Module.finrank ℂ (cmEigenspace ι τ') :=
  Nat.eq_of_mul_eq_mul_right Module.finrank_pos
    ((spec_a2a_finrank ι τ).trans (spec_a2a_finrank ι τ').symm)

/-- **S5, the embeddings over `σ`.** For `u ∈ L` with `u² = -d`, `d > 0`, exactly half of the
embeddings `τ : L → ℂ` send `u` to `i√d`: each of the `e = [L : ℚ] / 2` real places of `F`
contributes one.
Source: PW v0.3, Subsection 2.3 ("Each real place `v` of `F` has a unique extension `σ_v` of
`σ` to `L`"); Lang, *Algebra*, Ch. V, Thm. 4.1 (`[L : k]` extensions of each embedding of `k`). -/
theorem spec_a2a_card_plus (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    Nat.card {τ : L →ₐ[ℚ] ℂ // τ u = HodgeBlocks.WeilAction.omegaC d} * 2 =
      Module.finrank ℚ L :=
  spec_a2a_card_plus_aux u hd hu

example (u : L) (hu : u ^ 2 = algebraMap ℚ L (-3)) :
    Nat.card {τ : L →ₐ[ℚ] ℂ // τ u = HodgeBlocks.WeilAction.omegaC 3} * 2 =
      Module.finrank ℚ L :=
  spec_a2a_card_plus u (by norm_num) hu

/-- **S6, eigenspaces of one element.** For `u ∈ L` and `ω ∈ ℂ`, the sum of the `W_τ` with
`τ(u) = ω` is the `ω`-eigenspace of `ι(u)_ℂ`.
Source: PW v0.3, Subsection 2.2 (`V_ℂ = W ⊕ W̄`, the eigenspace decomposition for `k`) and
Subsection 2.3 (`W` is the sum of the `W_v`); it follows from S1, S2 and `ι(u)_ℂ = τ(u)` on
`W_τ`. -/
theorem spec_a2a_iSup_eq_eigenspace [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (u : L) (ω : ℂ) :
    ⨆ (τ : L →ₐ[ℚ] ℂ) (_ : τ u = ω), cmEigenspace ι τ =
      Module.End.eigenspace ((ι u).baseChange ℂ) ω :=
  spec_a2a_iSup_eq_eigenspace_aux ι u ω

example [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) :
    cmPlusPart ι u d =
      Module.End.eigenspace ((ι u).baseChange ℂ) (HodgeBlocks.WeilAction.omegaC d) :=
  spec_a2a_iSup_eq_eigenspace ι u _

/-- **S7, `V₊ = Vs`.** For any Weil action `A` (on a weight-one rational Hodge structure on `V`)
whose operator is `J = ι(u)`, the sum `V₊` of the `W_τ` with `τ(u) = i√d` is `A.Vs`, the
`i√d`-eigenspace from which the Weil classes `A.weilClasses` are built.
Source: PW v0.3, Subsection 2.2 (`W` for the fixed embedding `σ`) and Subsection 2.3;
`HodgeBlocks.WeilAction.Vs` (`Blocks/Weil/Basic.lean`). -/
theorem spec_a2a_cmPlusPart_eq_Vs [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) :
    cmPlusPart ι u d = A.Vs :=
  spec_a2a_cmPlusPart_eq_Vs_aux ι A u hJ

example [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (τ : L →ₐ[ℚ] ℂ) (hτ : τ u = HodgeBlocks.WeilAction.omegaC d) :
    cmEigenspace ι τ ≤ A.Vs :=
  spec_a2a_cmPlusPart_eq_Vs ι A u hJ ▸ le_iSup₂_of_le τ hτ le_rfl

variable [IsCMField L]

/-- **S9, orthogonality.** For a CM field `L` with complex conjugation `c` and a form with
`E(ι(a) x, y) = E(x, ι(c a) y)`, `E_ℂ(W_τ, W_τ') = 0` unless `τ' = τ̄ = conj ∘ τ`.
Source: PW v0.3, Subsection 2.3 ("The Rosati involution of every polarization induces complex
conjugation on `L`"; "The polarization identifies `W̄_v` with `W_v^∨`"); Birkenhake–Lange,
*Complex Abelian Varieties*, §5.5. -/
theorem spec_a2a_orthogonal (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ τ' : L →ₐ[ℚ] ℂ) (h : τ' ≠ cmConjEmbedding τ)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) (y : ℂ ⊗[ℚ] V) (hy : y ∈ cmEigenspace ι τ') :
    E.baseChange ℂ x y = 0 :=
  spec_a2a_orthogonal_aux ι E hRos τ τ' h x hx y hy

/-- **S10, duality.** For a CM field `L`, a nondegenerate form with
`E(ι(a) x, y) = E(x, ι(c a) y)`, and finite-dimensional `V`, the pairing
`W_τ̄ → W_τ^∨`, `y ↦ (x ↦ E_ℂ(x, y))`, is bijective: `W_τ̄ ≅ W_τ^∨`.
Source: PW v0.3, Subsection 2.3 ("The polarization identifies `W̄_v` with `W_v^∨`") and proof of
Theorem 4.2, first paragraph; `WeilPower.crossPairing` (`Foundations/WeilPower.lean`), the case
`L = k`, `d = 3` being `WeilPower.weilDuality`. -/
theorem spec_a2a_duality_bijective [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ : L →ₐ[ℚ] ℂ) :
    Function.Bijective (WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
      (cmEigenspace ι (cmConjEmbedding τ))) :=
  spec_a2a_duality_bijective_aux ι E hE hRos τ

example [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ : L →ₐ[ℚ] ℂ) :
    cmEigenspace ι (cmConjEmbedding τ) ≃ₗ[ℂ] Module.Dual ℂ (cmEigenspace ι τ) :=
  LinearEquiv.ofBijective _ (spec_a2a_duality_bijective ι E hE hRos τ)

/-- **S12, falsification: orthogonality needs the Rosati condition.** On `V = L × L` with the
diagonal action and the nondegenerate alternating trace form
`E((x₁, x₂), (y₁, y₂)) = Tr(x₁ y₂) - Tr(x₂ y₁)`, which satisfies `E(a x, y) = E(x, a y)` (the
compatibility for the identity, not for complex conjugation), the conclusion of S9 fails:
some `W_τ` and `W_τ'` with `τ' ≠ τ̄` pair nontrivially.
Source: constructed here; compare PW v0.3, Subsection 2.3 (the Rosati involution induces complex
conjugation on `L`). -/
theorem spec_a2a_orthogonal_fails_without_rosati :
    (a2a_traceSymplectic L).Nondegenerate ∧ (a2a_traceSymplectic L).IsAlt ∧
      (∀ (a : L) (x y : L × L),
        a2a_traceSymplectic L (a2a_diagAction L a x) y =
          a2a_traceSymplectic L x (a2a_diagAction L a y)) ∧
      ∃ τ τ' : L →ₐ[ℚ] ℂ, τ' ≠ cmConjEmbedding τ ∧
        ∃ x ∈ cmEigenspace (a2a_diagAction L) τ, ∃ y ∈ cmEigenspace (a2a_diagAction L) τ',
          (a2a_traceSymplectic L).baseChange ℂ x y ≠ 0 :=
  spec_a2a_orthogonal_fails_without_rosati_aux

example : ¬ ∀ τ τ' : L →ₐ[ℚ] ℂ, τ' ≠ cmConjEmbedding τ →
    ∀ x ∈ cmEigenspace (a2a_diagAction L) τ, ∀ y ∈ cmEigenspace (a2a_diagAction L) τ',
      (a2a_traceSymplectic L).baseChange ℂ x y = 0 := by
  intro hall
  obtain ⟨-, -, -, τ, τ', hne, x, hx, y, hy, hxy⟩ :=
    spec_a2a_orthogonal_fails_without_rosati (L := L)
  exact hxy (hall τ τ' hne x hx y hy)

end NumberField

end HodgeLean.Foundations
