import HodgeLean.Adapters.HodgeHigherDegreeAbelianProofs

/-! # Toward the Hodge decomposition in degrees `n ≥ 2` for abelian `X`: frozen specification

Inputs stage 4m (`docs/specs/HodgeHigherDegreeAbelian.md`). Stage 4l proved the degree-one Hodge
decomposition for every abelian `X`, and degree `0` holds for every `X`. The ledger hypothesis
`HodgeDecomposition X` asks for every degree. This stage freezes the first stage of the
multiplicative route, `H^n = ⋀^n H¹` through the torus theorem: the decomposition of `⋀^n H¹`
induced by degree one, transported to `H_dR^n(X)`, and the implication from the multiplicativity of
the Hodge filtration (`CupFiltered`, an existing named input) together with the opposedness of
upstream's filtrations in degrees `2 ≤ n ≤ 2g` to `HodgeDecomposition X`.

Claimed:
* for abelian `X`: `HodgeDecomposition X` is equivalent to the decomposition in degrees `n ≥ 2`;
  `H_dR^n(X) = 0` and the decomposition holds for `n > 2g`; so the decomposition in degrees
  `2 ≤ n ≤ 2g` implies `HodgeDecomposition X`;
* pure linear algebra: an internal family `W` on the line `p + q = n` that lies under two
  decreasing filtrations `F`, `G` with `F^p ∩ G^{n+1-p} = 0` is exactly `F^p ∩ G^{n-p}`;
* for every cup product `μ`: the cup-wedge pieces `cupWedgePiece X μ n` vanish off the line
  `p + q = n`, and conjugation swaps the `(p, q)` and `(q, p)` pieces;
* for abelian `X` and `μ` with `TorusCohomology μ`: the cup-wedge pieces are the image of the
  pieces of `⋀^n` of the weight-one structure, and they form an internal direct sum of
  `H_dR^n(X)`, with no Hodge-theoretic input;
* the implication from `CupFiltered X μ` to `cupWedgePiece ≤ deRhamHodgePiece`; and, with the torus
  theorem, the equivalence of the degree-`n` decomposition with `deRhamHodgePiece ≤ cupWedgePiece`;
* the implication from `CupFiltered X μ`, `TorusCohomology μ` and `F^p ∩ conj F^{n+1-p} = 0`
  (`1 ≤ p ≤ n`) to `deRhamHodgePiece X n = cupWedgePiece X μ n` and the degree-`n` decomposition;
  with this for `2 ≤ n ≤ 2g`, the implication to `HodgeDecomposition X`.

Not claimed: `CupFiltered X μ` for any `μ`, the opposedness of upstream's filtrations in any degree
`n ≥ 2`, the degree-`n` decomposition for any `n` with `2 ≤ n ≤ 2g`, `HodgeDecomposition X` itself,
or anything for non-abelian `X`. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- **Only degrees `n ≥ 2` remain.** For abelian `X`, `HodgeDecomposition X` holds exactly when the
pieces `deRhamHodgePiece X n` form an internal direct sum for every `n ≥ 2`: degree `0` is
`deRhamHodgePiece_isInternal_zero` and degree `1` is stage 4l.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1
(degree one); `deRhamHodgePiece_isInternal_zero` and `spec_deRhamHodgePiece_one_isInternal`. -/
theorem spec_hodgeDecomposition_iff_two_le (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    HodgeDecomposition X ↔
      ∀ n : ℕ, 2 ≤ n → DirectSum.IsInternal (deRhamHodgePiece X n) :=
  spec_hodgeDecomposition_iff_two_le_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hD : HodgeDecomposition X) :
    DirectSum.IsInternal (deRhamHodgePiece X 2) :=
  (spec_hodgeDecomposition_iff_two_le X).mp hD 2 le_rfl

/-- **De Rham cohomology vanishes above `2g`.** For abelian `X` and `n > 2 · dim X`,
`H_dR^n(X) = 0`: `H^n(X(ℂ); ℚ) = 0` (`vanishingAboveTop_abelian`, from the torus theorem), and
`bettiDeRhamHQ X n` is surjective (`spec_bettiDeRhamIso_abelian`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
`torusCohomology_cupProductOf`, `vanishingAboveTop_of_torusCohomology` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_subsingleton_deRhamCohomology_of_lt (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (hn : 2 * dim X.left < n) :
    Subsingleton H_dR^(n : ℤ)(X) :=
  spec_subsingleton_deRhamCohomology_of_lt_aux X n hn

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (α : H_dR^((2 * dim X.left + 1 : ℕ) : ℤ)(X)) : α = 0 :=
  (spec_subsingleton_deRhamCohomology_of_lt X _ (Nat.lt_succ_self _)).elim α 0

/-- **The decomposition holds above `2g`.** For abelian `X` and `n > 2 · dim X`, the pieces
`deRhamHodgePiece X n` form an internal direct sum, because `H_dR^n(X) = 0`.
Source: `spec_subsingleton_deRhamCohomology_of_lt`; Mathlib's `DirectSum.IsInternal`. -/
theorem spec_deRhamHodgePiece_isInternal_of_lt (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (hn : 2 * dim X.left < n) :
    DirectSum.IsInternal (deRhamHodgePiece X n) :=
  spec_deRhamHodgePiece_isInternal_of_lt_aux X n hn

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    DirectSum.IsInternal (deRhamHodgePiece X (2 * dim X.left + 1)) :=
  spec_deRhamHodgePiece_isInternal_of_lt X _ (Nat.lt_succ_self _)

/-- **A binder strictly smaller than `HodgeDecomposition X`.** For abelian `X`, the decomposition
in the finitely many degrees `2 ≤ n ≤ 2 · dim X` implies `HodgeDecomposition X`: degrees `0` and
`1` are proved, and degrees above `2g` are `spec_deRhamHodgePiece_isInternal_of_lt`.
Source: `spec_hodgeDecomposition_iff_two_le` and `spec_deRhamHodgePiece_isInternal_of_lt`. -/
theorem spec_hodgeDecomposition_of_isInternal_le (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → DirectSum.IsInternal (deRhamHodgePiece X n)) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_isInternal_le_aux X h

/-- The binder is implied by `HodgeDecomposition X`, so the two are equivalent. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    HodgeDecomposition X ↔
      ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → DirectSum.IsInternal (deRhamHodgePiece X n) :=
  ⟨fun hD n _ _ => hD.isInternal n, spec_hodgeDecomposition_of_isInternal_le X⟩

/-- **Opposed filtrations pin down the pieces (linear algebra).** Let `W` be an internal family of
submodules supported on the line `p + q = n`, and `F`, `G` decreasing filtrations with
`W (p, q) ≤ F p ⊓ G q`. If `F p ⊓ G (n + 1 - p) = ⊥` for every `p`, then
`F p ⊓ G (n - p) = W (p, n - p)`. Write `x ∈ F p ⊓ G (n - p)` as `∑ w_{p'}`. The part with
`p' < p` lies in `F p` and in `G (n + 1 - p)`, so it is `0`; the part with `p' > p` lies in
`F (p + 1)` and in `G (n - p)`, so it is `0`; hence `x = w_p`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2 (Hodge structures as
pairs of `n`-opposed filtrations); Mathlib's `DirectSum.IsInternal`. -/
theorem spec_inf_eq_of_opposed {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℤ) {W : ℤ × ℤ → Submodule R M} (hW : DirectSum.IsInternal W)
    (hW0 : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → W pq = ⊥) {F G : ℤ → Submodule R M}
    (hF : Antitone F) (hG : Antitone G) (hle : ∀ pq : ℤ × ℤ, W pq ≤ F pq.1 ⊓ G pq.2)
    (hopp : ∀ p : ℤ, F p ⊓ G (n + 1 - p) = ⊥) (p : ℤ) :
    F p ⊓ G (n - p) = W (p, n - p) :=
  spec_inf_eq_of_opposed_aux n hW hW0 hF hG hle hopp p

/-- The conclusion read as an upper bound: `F p ⊓ G (n - p)` lies in the piece `W (p, n - p)`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (n : ℤ) {W : ℤ × ℤ → Submodule R M} (hW : DirectSum.IsInternal W)
    (hW0 : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → W pq = ⊥) {F G : ℤ → Submodule R M}
    (hF : Antitone F) (hG : Antitone G) (hle : ∀ pq : ℤ × ℤ, W pq ≤ F pq.1 ⊓ G pq.2)
    (hopp : ∀ p : ℤ, F p ⊓ G (n + 1 - p) = ⊥) (p : ℤ) :
    F p ⊓ G (n - p) ≤ W (p, n - p) :=
  (spec_inf_eq_of_opposed n hW hW0 hF hG hle hopp p).le

/-- **Cup-wedge pieces live on the line `p + q = n`.** For every cup product `μ`,
`cupWedgePiece X μ n pq = ⊥` when `pq.1 + pq.2 ≠ n`. A generator with every `d i` on the line
`p + q = 1` has total type on the line `p + q = n`; otherwise some `v i` lies in a `⊥` piece, so
`v i = 0` and the multilinear `cupMultiC` vanishes.
Source: `cupWedgePiece`, `cohomologyHodgePiece` and Mathlib's `MultilinearMap.map_coord_zero`. -/
theorem spec_cupWedgePiece_eq_bot (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) (n : ℕ) (pq : ℤ × ℤ) (h : pq.1 + pq.2 ≠ n) :
    cupWedgePiece X μ n pq = ⊥ :=
  spec_cupWedgePiece_eq_bot_aux X μ n pq h

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) : cupWedgePiece X μ 2 (3, 0) = ⊥ :=
  spec_cupWedgePiece_eq_bot X μ 2 (3, 0) (by norm_num)

/-- **Conjugation swaps the cup-wedge pieces.** For every cup product `μ`, if `α` lies in the
`(p, q)` cup-wedge piece, then `deRhamConj X n α` lies in the `(q, p)` piece. Rational conjugation
`sigmaQ` commutes with `cupC` (`CupProduct.sigmaQ_cupC`), hence with `cupMultiC`, it swaps the
degree-one pieces (`cohomologyHodgePiece_map_sigmaQ`), and `bettiDeRhamHQ` intertwines it with
`deRhamConj` (`bettiDeRhamHQ_sigmaQ`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.2
(`conj H^{p,q} = H^{q,p}`); `CupProduct.sigmaQ_cupC`, `cohomologyHodgePiece_map_sigmaQ` and
`bettiDeRhamHQ_sigmaQ`. -/
theorem spec_deRhamConj_mem_cupWedgePiece (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (μ : CupProduct X) (n : ℕ) (p q : ℤ)
    {α : H_dR^(n : ℤ)(X)} (hα : α ∈ cupWedgePiece X μ n (p, q)) :
    deRhamConj X n α ∈ cupWedgePiece X μ n (q, p) :=
  spec_deRhamConj_mem_cupWedgePiece_aux X μ n p q hα

/-- The `(p, p)` piece is stable under conjugation. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (n : ℕ) (p : ℤ) {α : H_dR^(n : ℤ)(X)}
    (hα : α ∈ cupWedgePiece X μ n (p, p)) :
    deRhamConj X n α ∈ cupWedgePiece X μ n (p, p) :=
  spec_deRhamConj_mem_cupWedgePiece X μ n p p hα

/-- **The cup-wedge pieces are the transported exterior-power pieces.** For abelian `X` and a cup
product `μ` with the torus theorem, the `(p, q)` cup-wedge piece is the image of the `(p, q)` piece
of `⋀^n` of the weight-one structure `abelianWeightOneHodgeStructure X` under the complexified torus
isomorphism followed by `bettiDeRhamHQ X n`. Each exterior-power piece is the span of its wedges
(`exteriorPowerH_eq_wedgePiece`), and the complexified torus isomorphism sends a wedge
`x₁ ∧ ⋯ ∧ x_n` to `cupMultiC n x` (`TorusCohomology.complexificationCongr_symm_ιMulti`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
`exteriorPowerH_eq_wedgePiece` and `TorusCohomology.complexificationCongr_symm_ιMulti`
(`RealDefs/AbelianExterior.lean`). -/
theorem spec_cupWedgePiece_eq_map_exteriorPowerH (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (n : ℕ) (pq : ℤ × ℤ) :
    letI := (finiteBetti_abelian X).finite 1
    letI := (finiteBetti_abelian X).finite n
    cupWedgePiece X μ n pq =
      ((abelianWeightOneHodgeStructure X).exteriorPowerH (V := HQ X 1) n pq).map
        (bettiDeRhamHQ X n ∘ₗ
          (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^n (HQ X 1))
            (W := HQ X n) (hT.cupWedgeEquiv n)).toLinearMap) :=
  spec_cupWedgePiece_eq_map_exteriorPowerH_aux X hT n pq

/-- Every cup-wedge piece lies in the range of the transport map. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) (n : ℕ) (pq : ℤ × ℤ) :
    letI := (finiteBetti_abelian X).finite 1
    letI := (finiteBetti_abelian X).finite n
    cupWedgePiece X μ n pq ≤ LinearMap.range (bettiDeRhamHQ X n ∘ₗ
      (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^n (HQ X 1))
        (W := HQ X n) (hT.cupWedgeEquiv n)).toLinearMap) := by
  rw [spec_cupWedgePiece_eq_map_exteriorPowerH X hT n pq]
  exact LinearMap.map_le_range

/-- **The transported decomposition (Betti-side route).** For abelian `X` and a cup product `μ`
with the torus theorem, the cup-wedge pieces form an internal direct sum of `H_dR^n(X)`, with no
Hodge-theoretic input beyond stage 4l: they are the image of the internal family
`exteriorPowerH_isInternal` under the linear equivalence `bettiDeRhamHQ X n ∘ Φ`
(`spec_bettiDeRhamIso_abelian`, `TorusCohomology.bijective`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
§1.4; `spec_cupWedgePiece_eq_map_exteriorPowerH`, `QHodgeStructure.exteriorPowerH_isInternal`
and `spec_bettiDeRhamIso_abelian`. -/
theorem spec_cupWedgePiece_isInternal (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (n : ℕ) :
    DirectSum.IsInternal (cupWedgePiece X μ n) :=
  spec_cupWedgePiece_isInternal_aux X hT n

/-- With the instantiated cup product, whose torus theorem is proved. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) :
    ⨆ pq, cupWedgePiece X (cupProductOf X) n pq = ⊤ :=
  (spec_cupWedgePiece_isInternal X (torusCohomology_cupProductOf X) n).submodule_iSup_eq_top

/-- **Multiplicativity puts the cup-wedge pieces inside the Hodge pieces.** The implication from
`CupFiltered X μ` (O5): each cup-wedge piece lies in the matching `deRhamHodgePiece X n`. On the line
this is `CupFiltered.bettiDeRhamHQ_cupMultiC_mem`; off the line both sides are `⊥`
(`spec_cupWedgePiece_eq_bot`).
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§7.1 (through `CupFiltered`); `CupFiltered.bettiDeRhamHQ_cupMultiC_mem`. -/
theorem spec_cupWedgePiece_le_deRhamHodgePiece (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hC : CupFiltered X μ) (n : ℕ)
    (pq : ℤ × ℤ) :
    cupWedgePiece X μ n pq ≤ deRhamHodgePiece X n pq :=
  spec_cupWedgePiece_le_deRhamHodgePiece_aux X hC n pq

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hC : CupFiltered X μ) (n : ℕ) (d : Fin n → ℤ × ℤ)
    (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (hv : ∀ i, v i ∈ cohomologyHodgePiece X 1 (d i)) :
    bettiDeRhamHQ X n (μ.cupMultiC n v) ∈ deRhamHodgePiece X n (HodgeBlocks.totalBidegree n d) :=
  spec_cupWedgePiece_le_deRhamHodgePiece X hC n _ (Submodule.subset_span ⟨d, v, rfl, hv, rfl⟩)

/-- **The exact gap in degree `n`.** For abelian `X` and a cup product `μ` with the torus theorem
and `CupFiltered X μ`, the degree-`n` decomposition holds exactly when every Hodge piece lies in
the matching cup-wedge piece. `→`: the cup-wedge pieces span (`spec_cupWedgePiece_isInternal`),
lie in the Hodge pieces (`spec_cupWedgePiece_le_deRhamHodgePiece`), and the Hodge pieces are
independent, so `mem_of_map_mem_of_iSupIndep_of_map_le` applies with `f = id`. `←`: the two
families are equal, and the cup-wedge family is internal.
Source: `spec_cupWedgePiece_isInternal`, `spec_cupWedgePiece_le_deRhamHodgePiece` and
`mem_of_map_mem_of_iSupIndep_of_map_le` (`RealDefs/CupFiltered.lean`). -/
theorem spec_isInternal_iff_le_cupWedgePiece (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) :
    DirectSum.IsInternal (deRhamHodgePiece X n) ↔
      ∀ pq : ℤ × ℤ, deRhamHodgePiece X n pq ≤ cupWedgePiece X μ n pq :=
  spec_isInternal_iff_le_cupWedgePiece_aux X hT hC n

/-- Under `HodgeDecomposition X`, the Hodge pieces are the cup-wedge pieces in every degree. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) (hC : CupFiltered X μ)
    (hD : HodgeDecomposition X) (n : ℕ) (pq : ℤ × ℤ) :
    deRhamHodgePiece X n pq = cupWedgePiece X μ n pq :=
  le_antisymm ((spec_isInternal_iff_le_cupWedgePiece X hT hC n).mp (hD.isInternal n) pq)
    (spec_cupWedgePiece_le_deRhamHodgePiece X hC n pq)

/-- **Opposed filtrations give the Hodge pieces in degree `n`.** For abelian `X` and a cup product
`μ` with the torus theorem and `CupFiltered X μ`, if `F^p ∩ conj F^{n+1-p} = 0` in
`H_dR^n(X)` for `1 ≤ p ≤ n`, then `deRhamHodgePiece X n = cupWedgePiece X μ n`. Apply
`spec_inf_eq_of_opposed` with `W = cupWedgePiece X μ n` (internal, supported on the line),
`F p = F^p H_dR^n(X)` and `G q = conj F^q H_dR^n(X)` (both decreasing). The opposedness for `p ≤ 0`
and `p > n` is automatic (`hodgeFiltration_eq_top_of_nonpos`, `hodgeFiltration_eq_bot_of_lt`,
`conjHodgeFiltration_eq_bot_of_lt`).
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1; `spec_inf_eq_of_opposed`,
`spec_cupWedgePiece_isInternal` and `spec_cupWedgePiece_le_deRhamHodgePiece`. -/
theorem spec_deRhamHodgePiece_eq_cupWedgePiece_of_opposed (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ)
    (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    deRhamHodgePiece X n = cupWedgePiece X μ n :=
  spec_deRhamHodgePiece_eq_cupWedgePiece_of_opposed_aux X hT hC n hopp

/-- In degree `0` the opposedness binder is vacuous. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X)) :
    deRhamHodgePiece X 0 = cupWedgePiece X (cupProductOf X) 0 :=
  spec_deRhamHodgePiece_eq_cupWedgePiece_of_opposed X (torusCohomology_cupProductOf X) hC 0
    (fun p h1 h2 => absurd (h1.trans h2) (by norm_num))

/-- **The degree-`n` decomposition from opposed filtrations.** For abelian `X` and a cup product
`μ` with the torus theorem and `CupFiltered X μ`: if `F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)`
for `1 ≤ p ≤ n`, the pieces `deRhamHodgePiece X n` form an internal direct sum.
Source: `spec_deRhamHodgePiece_eq_cupWedgePiece_of_opposed` and `spec_cupWedgePiece_isInternal`. -/
theorem spec_deRhamHodgePiece_isInternal_of_opposed (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ)
    (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    DirectSum.IsInternal (deRhamHodgePiece X n) :=
  spec_deRhamHodgePiece_isInternal_of_opposed_aux X hT hC n hopp

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X))
    (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ 2 → hodgePiece X p (2 + 1 - p) 2 = ⊥) :
    DirectSum.IsInternal (deRhamHodgePiece X 2) :=
  spec_deRhamHodgePiece_isInternal_of_opposed X (torusCohomology_cupProductOf X) hC 2
    (by exact_mod_cast hopp)

/-- **`HodgeDecomposition X` from multiplicativity and opposedness.** For abelian `X` and a cup
product `μ` with the torus theorem: the implication from `CupFiltered X μ` and
`F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)` for `2 ≤ n ≤ 2 · dim X` and `1 ≤ p ≤ n` to
`HodgeDecomposition X`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1; Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_hodgeDecomposition_of_isInternal_le` and `spec_deRhamHodgePiece_isInternal_of_opposed`. -/
theorem spec_hodgeDecomposition_of_opposed (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ)
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_opposed_aux X hT hC hopp

/-- With the instantiated cup product, the open inputs are `CupFiltered` and the opposedness. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_opposed X (torusCohomology_cupProductOf X) hC hopp

end HodgeLean.Adapters
