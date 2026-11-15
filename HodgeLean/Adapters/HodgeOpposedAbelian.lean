import HodgeLean.Adapters.HodgeOpposedAbelianProofs

/-! # Opposedness of the Hodge filtrations for abelian `X`, stage 1: frozen specification

Opposedness stage 1 (`docs/specs/HodgeOpposedAbelian.md`). Stage 4m reduced `HodgeDecomposition X`
for abelian `X` to two inputs: the multiplicativity `CupFiltered X μ` (O5) and the opposedness
`F^p ∩ conj F^{n+1-p} = 0` of upstream's filtrations in degrees `2 ≤ n ≤ 2g`. This stage shows
that, for abelian `X`, **the second input follows from the first**, with no dimension count and no
coherent cohomology. The argument is Poincaré duality on the cup-wedge pieces of stage 4m. Since
`Ω^{g+1} = 0`, `F^{g+1} H^{2g} = 0`. Multiplicativity then makes `F^p H^n` orthogonal to
`F^{g+1-p} H^{2g-n}`, which contains the cup-wedge pieces `W(a, ·)` with `a ≥ g + 1 - p`. The
duality of the exterior algebra pairs `W(p', n - p')` perfectly with `W(g - p', ·)`. So `F^p H^n`
has no component of type `p' < p`, and this upper bound gives opposedness.

Claimed:
* for every integral smooth `X`: the opposedness condition is symmetric under conjugation, the
  pieces `F^p ⊓ conj F^q` vanish for `p > dim X` or `q > dim X`, opposedness holds in every degree
  `n ≥ 2 · dim X`, and in degree `n` it is equivalent to the reduced condition over
  `max(1, n + 1 - dim X) ≤ p ≤ (n + 1) / 2`, a binder strictly smaller than opposedness and free of
  `CupFiltered`;
* for abelian `X` and every cup product `μ`: the product of a `(a, b)` and a `(c, d)` cup-wedge
  class lies in the `(a + c, b + d)` cup-wedge piece;
* for abelian `X` and `μ` with the torus theorem: Poincaré duality for the complexified cup
  product, the vanishing of the top-degree cup-wedge pieces off `(g, g)`, and the typed duality
  between `W(a, ·)` and `W(g - a, ·)`;
* also with the torus theorem: the implication from the upper bound
  `F^p H^n ≤ ⨆_{p' ≥ p} W(p', n - p')` to opposedness in degree `n`, with no `CupFiltered`;
* the implication from `CupFiltered X μ` and the torus theorem to that upper bound, to
  `F^p H^n = ⨆_{p' ≥ p} W(p', n - p')`, to opposedness in every degree, and to
  `HodgeDecomposition X`.

Not claimed: `CupFiltered X μ` for any `μ`; opposedness in any degree `2 ≤ n < 2 · dim X` without
`CupFiltered`; any dimension of `F^p H_dR^n(X)` or of `H^q(X(ℂ), Ω^p)`; `HodgeDecomposition X`
itself; anything for non-abelian `X` beyond the first four statements. HC no distance; AV
milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- **Opposedness is symmetric under conjugation.** For every integral smooth `X`,
`F^p ⊓ conj F^q = 0` in `H_dR^n(X)` exactly when `F^q ⊓ conj F^p = 0`: the conjugate-linear
involution `deRhamConj` (`deRhamConj_deRhamConj`) maps the first intersection onto the second.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; upstream `deRhamConj`,
`conjHodgeFiltrationComplexSubmodule` and `deRhamConj_deRhamConj` (`RealDefs/Filtration.lean`). -/
theorem spec_hodgePiece_eq_bot_comm (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p q n : ℤ) :
    hodgePiece X p q n = ⊥ ↔ hodgePiece X q p n = ⊥ :=
  spec_hodgePiece_eq_bot_comm_aux X p q n

/-- With `p = q` the statement is trivial; in degree `n` it trades `(p, n + 1 - p)` for
`(n + 1 - p, p)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n p : ℤ)
    (h : hodgePiece X (n + 1 - p) p n = ⊥) :
    hodgePiece X p (n + 1 - p) n = ⊥ :=
  (spec_hodgePiece_eq_bot_comm X p (n + 1 - p) n).mpr h

/-- **The pieces vanish above the dimension.** For every integral smooth `X`, if `p > dim X` or
`q > dim X`, then `F^p ⊓ conj F^q = 0` in every degree: `F^p = 0` for `p > dim X`
(`spec_hodgeFiltration_eq_bot_of_dim_lt`, from `Ω^p = 0`), and `conj F^q` is the preimage of `0`
under the injective `deRhamConj`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.3.1; `spec_hodgeFiltration_eq_bot_of_dim_lt` (`CurveStructureSheafVanishing.lean`) and
`deRhamConj_deRhamConj`. -/
theorem spec_hodgePiece_eq_bot_of_dim_lt (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p q n : ℤ) (h : (dim X.left : ℤ) < p ∨ (dim X.left : ℤ) < q) :
    hodgePiece X p q n = ⊥ :=
  spec_hodgePiece_eq_bot_of_dim_lt_aux X p q n h

/-- On a curve, `F^2 ⊓ conj F^0 = 0` in every degree. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] (n : ℤ) :
    hodgePiece X 2 0 n = ⊥ :=
  spec_hodgePiece_eq_bot_of_dim_lt X 2 0 n
    (Or.inl (by rw [SmoothOfRelativeDimension.dim_eq X.hom 1]; norm_num))

/-- **Opposedness in degrees `n ≥ 2 · dim X` is automatic.** For every integral smooth `X` and
`n ≥ 2g`, `F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)` for all `p`, since `p + (n + 1 - p) > 2g`
forces `p > g` or `n + 1 - p > g` (`spec_hodgePiece_eq_bot_of_dim_lt`). In particular stage 4m's
binder needs no degree `2g`.
Source: `spec_hodgePiece_eq_bot_of_dim_lt`. -/
theorem spec_opposed_of_two_mul_dim_le (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) (hn : 2 * dim X.left ≤ n) :
    ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ :=
  spec_opposed_of_two_mul_dim_le_aux X n hn

/-- The top degree `n = 2g`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    ∀ p : ℤ, 1 ≤ p → p ≤ ((2 * dim X.left : ℕ) : ℤ) →
      hodgePiece X p (((2 * dim X.left : ℕ) : ℤ) + 1 - p) (2 * dim X.left : ℕ) = ⊥ :=
  spec_opposed_of_two_mul_dim_le X _ le_rfl

/-- **The reduced opposedness binder.** For every integral smooth `X` and every `n`, opposedness in
degree `n` (over `1 ≤ p ≤ n`) is equivalent to the same condition over
`max(1, n + 1 - dim X) ≤ p` and `2p ≤ n + 1`. The other indices follow from
`spec_hodgePiece_eq_bot_of_dim_lt` (one of `p`, `n + 1 - p` exceeds `dim X`) or from
`spec_hodgePiece_eq_bot_comm` (exchange `p` and `n + 1 - p`). For `n ≥ 2 · dim X` the reduced
condition is empty. No `CupFiltered` enters.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_hodgePiece_eq_bot_comm` and `spec_hodgePiece_eq_bot_of_dim_lt`. -/
theorem spec_opposed_iff_reduced (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (n : ℕ) :
    (∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) ↔
      (∀ p : ℤ, 1 ≤ p → (n : ℤ) + 1 - dim X.left ≤ p → 2 * p ≤ (n : ℤ) + 1 →
        hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :=
  spec_opposed_iff_reduced_aux X n

/-- On a surface (`dim X = 2`), opposedness in degree `2` reduces to `F^1 ∩ conj F^2 = 0`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 2 X.hom] (h : hodgePiece X 1 2 2 = ⊥) :
    ∀ p : ℤ, 1 ≤ p → p ≤ ((2 : ℕ) : ℤ) → hodgePiece X p (((2 : ℕ) : ℤ) + 1 - p) (2 : ℕ) = ⊥ := by
  refine (spec_opposed_iff_reduced X 2).mpr fun p h1 _ h2 => ?_
  obtain rfl : p = 1 := by omega
  exact h

/-- **Cup-wedge pieces multiply.** For abelian `X` and every cup product `μ`, if `bettiDeRhamHQ x`
lies in the `(a, b)` cup-wedge piece and `bettiDeRhamHQ y` in the `(c, d)` piece, then
`bettiDeRhamHQ (cupC x y)` lies in the `(a + c, b + d)` piece. `bettiDeRhamHQ` is injective
(`spec_bettiDeRhamIso_abelian`), so `x` and `y` are combinations of cup products of typed
degree-one classes; by associativity (`CupProduct.assoc`) the cup of two such products is the
product of the concatenated family, whose total type is the sum.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.3 (the
multiplicative structure of `⋀^• H¹`); `cupWedgePiece`, `CupProduct.assoc` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_cupC_mem_cupWedgePiece (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (μ : CupProduct X)
    {i j k : ℕ} (h : i + j = k) {a b c d : ℤ} {x : ℂ ⊗[ℚ] HQ X i} {y : ℂ ⊗[ℚ] HQ X j}
    (hx : bettiDeRhamHQ X i x ∈ cupWedgePiece X μ i (a, b))
    (hy : bettiDeRhamHQ X j y ∈ cupWedgePiece X μ j (c, d)) :
    bettiDeRhamHQ X k (μ.cupC h x y) ∈ cupWedgePiece X μ k (a + c, b + d) :=
  spec_cupC_mem_cupWedgePiece_aux X μ h hx hy

/-- Two typed degree-one classes multiply into the piece of the summed type. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) {x y : ℂ ⊗[ℚ] HQ X 1}
    (hx : bettiDeRhamHQ X 1 x ∈ cupWedgePiece X μ 1 (1, 0))
    (hy : bettiDeRhamHQ X 1 y ∈ cupWedgePiece X μ 1 (0, 1)) :
    bettiDeRhamHQ X 2 (μ.cupC (one_add_one_eq_two) x y) ∈ cupWedgePiece X μ 2 (1 + 0, 0 + 1) :=
  spec_cupC_mem_cupWedgePiece X μ one_add_one_eq_two hx hy

/-- **Poincaré duality for the complexified cup product.** For abelian `X` of dimension `g` and a
cup product `μ` with the torus theorem, and `i + j = 2g`: if `x ∪ y = 0` for every
`y ∈ ℂ ⊗ H^j`, then `x = 0`. Through the torus isomorphism this is the perfectness of the wedge
pairing `⋀^i V × ⋀^j V → ⋀^{2g} V` for `dim V = 2g` (on a basis, `e_I ∧ e_J = ± e_{all}` when `J`
is the complement of `I`, and `0` otherwise), with the associativity of `μ` identifying the cup
of two iterated cups with an iterated cup.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
Bourbaki, *Algèbre*, Ch. III §11 (duality for exterior powers); `TorusCohomology.bijective`,
`TorusCohomology.finrank_eq` and `CupProduct.assoc`. -/
theorem spec_eq_zero_of_forall_cupC_eq_zero (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) {i j : ℕ} (h : i + j = 2 * dim X.left) (x : ℂ ⊗[ℚ] HQ X i)
    (hx : ∀ y : ℂ ⊗[ℚ] HQ X j, μ.cupC h x y = 0) :
    x = 0 :=
  spec_eq_zero_of_forall_cupC_eq_zero_aux X hT h x hx

/-- With the instantiated cup product, whose torus theorem is proved. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : ℂ ⊗[ℚ] HQ X 0)
    (hx : ∀ y : ℂ ⊗[ℚ] HQ X (2 * dim X.left), (cupProductOf X).cupC (zero_add _) x y = 0) :
    x = 0 :=
  spec_eq_zero_of_forall_cupC_eq_zero X (torusCohomology_cupProductOf X) (zero_add _) x hx

/-- **The top-degree cup-wedge pieces are concentrated in type `(g, g)`.** For abelian `X` of
dimension `g` and `μ` with the torus theorem, `W(c, 2g - c) = 0` in degree `2g` for `c ≠ g`. The
degree-one pieces `(1, 0)` and `(0, 1)` both have dimension `g` (they are swapped by conjugation,
and `dim H¹ = 2g` by `TorusCohomology.finrank_eq`). A generator of type `(c, 2g - c)` is a cup of
`c` classes of type `(1, 0)` and `2g - c` of type `(0, 1)` (classes of other types are `0`); if
`c > g` or `2g - c > g`, some `g + 1` of them are linearly dependent, and `cupMultiC`, which is
alternating through `TorusCohomology.complexificationCongr_symm_ιMulti`, vanishes.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
§1.4; `TorusCohomology.complexificationCongr_symm_ιMulti` and `cohomologyHodgePiece_map_sigmaQ`. -/
theorem spec_cupWedgePiece_top_eq_bot (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (c : ℤ) (hc : c ≠ dim X.left) :
    cupWedgePiece X μ (2 * dim X.left) (c, ((2 * dim X.left : ℕ) : ℤ) - c) = ⊥ :=
  spec_cupWedgePiece_top_eq_bot_aux X hT c hc

/-- The `(g + 1, g - 1)` piece of `H^{2g}` vanishes. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    cupWedgePiece X (cupProductOf X) (2 * dim X.left)
      ((dim X.left : ℤ) + 1, ((2 * dim X.left : ℕ) : ℤ) - ((dim X.left : ℤ) + 1)) = ⊥ :=
  spec_cupWedgePiece_top_eq_bot X (torusCohomology_cupProductOf X) _ (by omega)

/-- **Typed Poincaré duality.** For abelian `X` of dimension `g`, `μ` with the torus theorem, and
`i + j = 2g`: if `bettiDeRhamHQ x` lies in the `(a, i - a)` cup-wedge piece and `x ∪ y = 0` for
every `y` whose image lies in the `(g - a, j - (g - a))` piece, then `x = 0`. Decompose an
arbitrary `y` along the internal family `cupWedgePiece X μ j` (`spec_cupWedgePiece_isInternal`,
with `bettiDeRhamHQ` bijective); the cup of `x` with the component of type `(c, j - c)` lies in
the top-degree piece of type `(a + c, ·)` (`spec_cupC_mem_cupWedgePiece`), which is `0` unless
`a + c = g` (`spec_cupWedgePiece_top_eq_bot`). So `x ∪ y = 0` for every `y`, and
`spec_eq_zero_of_forall_cupC_eq_zero` applies.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
statements 5–7 and `spec_cupWedgePiece_isInternal`. -/
theorem spec_eq_zero_of_cupC_cupWedgePiece (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) {i j : ℕ} (h : i + j = 2 * dim X.left) (a : ℤ)
    (x : ℂ ⊗[ℚ] HQ X i) (hx : bettiDeRhamHQ X i x ∈ cupWedgePiece X μ i (a, (i : ℤ) - a))
    (hxy : ∀ y : ℂ ⊗[ℚ] HQ X j,
      bettiDeRhamHQ X j y ∈
        cupWedgePiece X μ j ((dim X.left : ℤ) - a, (j : ℤ) - ((dim X.left : ℤ) - a)) →
      μ.cupC h x y = 0) :
    x = 0 :=
  spec_eq_zero_of_cupC_cupWedgePiece_aux X hT h a x hx hxy

/-- The untyped hypothesis implies the typed one, so this refines statement 6 on a piece. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) {i j : ℕ}
    (h : i + j = 2 * dim X.left) (a : ℤ) (x : ℂ ⊗[ℚ] HQ X i)
    (hx : bettiDeRhamHQ X i x ∈ cupWedgePiece X μ i (a, (i : ℤ) - a))
    (hxy : ∀ y : ℂ ⊗[ℚ] HQ X j, μ.cupC h x y = 0) :
    x = 0 :=
  spec_eq_zero_of_cupC_cupWedgePiece X hT h a x hx fun y _ => hxy y

/-- **Multiplicativity bounds the Hodge filtration from above.** For abelian `X` of dimension `g`,
the implication from `CupFiltered X μ` and the torus theorem to
`F^p H_dR^n(X) ≤ ⨆_{p' ≥ p} W(p', n - p')`. For `n > 2g` the space is `0`. Otherwise let
`α = β x ∈ F^p H^n`, with components `w_{p'}` along the cup-wedge pieces, and fix `p' < p`. Every
`y` of type `(g - p', ·)` in degree `2g - n` maps into `F^{g - p'} ≤ F^{g + 1 - p}`
(`spec_cupWedgePiece_le_deRhamHodgePiece`), so `x ∪ y` maps into `F^{g+1} H^{2g} = 0`
(`CupFiltered.mem`, `spec_hodgeFiltration_eq_bot_of_dim_lt`). The cups of the components with `y`
lie in distinct top-degree pieces (`spec_cupC_mem_cupWedgePiece`), which are independent, so each
vanishes, and `w_{p'} = 0` by `spec_eq_zero_of_cupC_cupWedgePiece`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1; Voisin, *Hodge Theory and
Complex Algebraic Geometry I*, §7.1 (through `CupFiltered`); statements 5–8. -/
theorem spec_hodgeFiltration_le_iSup_cupWedgePiece (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) ≤ ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') :=
  spec_hodgeFiltration_le_iSup_cupWedgePiece_aux X hT hC n p

/-- With the instantiated cup product: `F^1 H^2` lies in the span of the `(1, 1)` and `(2, 0)`
cup-wedge pieces and those of higher first index. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X)) :
    F^1 H_dR^((2 : ℕ) : ℤ)(X) ≤
      ⨆ (p' : ℤ) (_ : 1 ≤ p'), cupWedgePiece X (cupProductOf X) 2 (p', ((2 : ℕ) : ℤ) - p') :=
  spec_hodgeFiltration_le_iSup_cupWedgePiece X (torusCohomology_cupProductOf X) hC 2 1

/-- **The Hodge filtration is the filtration of the cup-wedge decomposition.** For abelian `X`,
the implication from `CupFiltered X μ` and the torus theorem to
`F^p H_dR^n(X) = ⨆_{p' ≥ p} W(p', n - p')`. `≤` is statement 9; `≥` holds because each
`W(p', n - p')` lies in `deRhamHodgePiece X n (p', n - p') ≤ F^{p'} ≤ F^p`
(`spec_cupWedgePiece_le_deRhamHodgePiece`, `hodgeFiltration_antitone`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
§1.4; statement 9 and `spec_cupWedgePiece_le_deRhamHodgePiece`. -/
theorem spec_hodgeFiltration_eq_iSup_cupWedgePiece (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) = ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') :=
  spec_hodgeFiltration_eq_iSup_cupWedgePiece_aux X hT hC n p

/-- In particular the top filtration step `F^n H^n` is the `(n, 0)` cup-wedge piece and those
above it. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X)) (n : ℕ) :
    cupWedgePiece X (cupProductOf X) n ((n : ℤ), (n : ℤ) - n) ≤ F^(n : ℤ) H_dR^(n : ℤ)(X) := by
  rw [spec_hodgeFiltration_eq_iSup_cupWedgePiece X (torusCohomology_cupProductOf X) hC n n]
  exact le_iSup₂_of_le (n : ℤ) le_rfl le_rfl

/-- **An inclusion upper bound gives opposedness, without `CupFiltered`.** For abelian `X` and `μ`
with the torus theorem, if `F^p H_dR^n(X) ≤ ⨆_{p' ≥ p} W(p', n - p')` for every `p`, then
`F^p ∩ conj F^{n+1-p} = 0` in degree `n` for every `p`. An `α` in the intersection lies in
`⨆_{p' ≥ p} W(p', n - p')`; its conjugate lies in `F^{n+1-p}`, so `α` lies in the conjugate of
`⨆_{p'' ≥ n+1-p} W(p'', n - p'')`, which is `⨆_{p' ≤ p-1} W(p', n - p')`
(`spec_deRhamConj_mem_cupWedgePiece`, `deRhamConj_deRhamConj`). The two spans meet in `0` because
the cup-wedge pieces are independent (`spec_cupWedgePiece_isInternal`).
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_deRhamConj_mem_cupWedgePiece` and `spec_cupWedgePiece_isInternal`. -/
theorem spec_opposed_of_hodgeFiltration_le (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (n : ℕ)
    (hF : ∀ p : ℤ,
      F^p H_dR^(n : ℤ)(X) ≤ ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p'))
    (p : ℤ) :
    hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ :=
  spec_opposed_of_hodgeFiltration_le_aux X hT n hF p

/-- The binder of stage 4m in degree `n`, from the upper bound alone. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ)
    (hF : ∀ p : ℤ, F^p H_dR^(n : ℤ)(X) ≤
      ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X (cupProductOf X) n (p', (n : ℤ) - p')) :
    ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ :=
  fun p _ _ => spec_opposed_of_hodgeFiltration_le X (torusCohomology_cupProductOf X) n hF p

/-- **Opposedness from multiplicativity.** For abelian `X`, the implication from `CupFiltered X μ`
and the torus theorem to `F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)`, for every `n` and `p`:
statements 9 and 11.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1; statements 9 and 11. -/
theorem spec_opposed_of_cupFiltered (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) (n : ℕ) (p : ℤ) :
    hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ :=
  spec_opposed_of_cupFiltered_aux X hT hC n p

/-- It discharges stage 4m's opposedness binder. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X)) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ :=
  fun n _ _ p _ _ => spec_opposed_of_cupFiltered X (torusCohomology_cupProductOf X) hC n p

/-- **`HodgeDecomposition X` from multiplicativity alone.** For abelian `X` and a cup product `μ`
with the torus theorem, the implication from `CupFiltered X μ` to `HodgeDecomposition X`: stage
4m's `spec_hodgeDecomposition_of_opposed` with its opposedness binder supplied by statement 12.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1; Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_hodgeDecomposition_of_opposed` and statement 12. -/
theorem spec_hodgeDecomposition_of_cupFiltered (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ) (hC : CupFiltered X μ) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupFiltered_aux X hT hC

/-- With the instantiated cup product, the only open input is `CupFiltered X (cupProductOf X)`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hC : CupFiltered X (cupProductOf X)) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupFiltered X (torusCohomology_cupProductOf X) hC

end HodgeLean.Adapters
