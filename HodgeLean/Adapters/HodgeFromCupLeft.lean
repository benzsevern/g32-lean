import HodgeLean.Adapters.HodgeFromCupLeftProofs

/-! # `HodgeDecomposition X` for abelian `X` from `hL` alone: frozen specification

Stage `HodgeFromCupLeft` (`docs/specs/HodgeFromCupLeft.md`). Stage `CupFilteredDeRham` (cupf1)
derived `CupFiltered X μ` and `HodgeDecomposition X` for abelian `X` from two inputs: the binder
`hL` and the opposedness `F^p ∩ conj F^{n+1-p} = 0` in degrees `2 ≤ n ≤ 2g`. Stage
`HodgeOpposedAbelian` (opp1) derived the opposedness from `CupFiltered X μ`. This stage runs
opp1's argument with `hL` in place of `CupFiltered`, so **`hL` alone suffices**.

`hL` is the special case of `CupFiltered` with a degree-one left factor of filtration level one:
if `β_1 x ∈ F^1 H^1` and `β_k y ∈ F^q H^k`, then `β_{1+k} (x ∪ y) ∈ F^{1+q} H^{1+k}`, where `β` is
`bettiDeRhamHQ`. It appears below as an explicit binder, written out in full.

The argument. Let `α ∈ F^p H^n` and `p' < p`. A generator `y` of the cup-wedge piece
`W(g - p', ·)` in degree `2g - n` is, up to sign, `U ∪ V` with `U` a cup of `g - p'` classes of
type `(1, 0)` (`spec_cupMultiC_comp_perm`, `cupMultiC_append`). Applying `hL` once per factor of
`U` puts `U ∪ α` into `F^{p + g - p'} ⊆ F^{g+1} = 0`, so `α ∪ U = 0` (graded commutativity), and
`α ∪ y = ±(α ∪ U) ∪ V = 0` (associativity). The `(1, 0)` factors are used before any `(0, 1)`
factor, so no multiplicativity beyond `hL` is needed. Opp1's typed Poincaré duality then kills the
component of `α` of type `p'`.

Claimed:
* for every cup product `μ`: the implication from `hL` to the iterated form, cup with `a` classes
  in `F^1 H^1` raises the filtration by `a`;
* for abelian `X` and every cup product `μ`: the implication from `hL` to the vanishing of
  `x ∪ (u_1 ∪ ⋯ ∪ u_a)` for `β x ∈ F^p H^n`, `β u_i ∈ F^1 H^1` and `p + a > dim X`;
* for abelian `X` and `μ` with the torus theorem: the implication from `hL` to the vanishing of
  `x ∪ y` for `β x ∈ F^p H^n`, `β y` in the cup-wedge piece `W(a, ·)` and `p + a > dim X`; the
  implication from `hL` to the upper bound
  `F^p H^n ≤ ⨆_{p' ≥ p} W(p', n - p')`, to opposedness in every degree, to `CupFiltered X μ` and to
  `HodgeDecomposition X`; and the equivalence of `CupFiltered X μ` with `hL`.

Not claimed: `hL` for any `μ`; `CupFiltered X μ` for any `μ`; opposedness in any degree
`2 ≤ n < 2 · dim X` without `hL`; `HodgeDecomposition X` itself; any dimension of `F^p H_dR^n(X)`;
anything for non-abelian `X` beyond the first statement. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- **Iterated `hL`.** For every cup product `μ`: the implication from `hL` to
`β_m ((u_1 ∪ ⋯ ∪ u_a) ∪ y) ∈ F^{a + q} H^m` whenever every `β_1 u_i ∈ F^1 H^1` and
`β_k y ∈ F^q H^k`. Induction on `a`: for `a = 0` the cup is the unit (`cupMultiC_zero`,
`CupProduct.one_cup`); for `a + 1`, `(u_0 ∪ M) ∪ y = u_0 ∪ (M ∪ y)` (`CupProduct.assoc`,
`CupProduct.cupMultiC_succ`), and `hL` adds one.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§7.1 (through `hL`); `CupProduct.cupMultiC_succ` and `CupProduct.assoc`. -/
theorem spec_bettiDeRhamHQ_cupC_cupMultiC_mem_of_cupLeft (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {a k m : ℕ} (h : a + k = m) (u : Fin a → ℂ ⊗[ℚ] HQ X 1)
    (hu : ∀ i, bettiDeRhamHQ X 1 (u i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X))
    (q : ℤ) (y : ℂ ⊗[ℚ] HQ X k) (hy : bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X)) :
    bettiDeRhamHQ X m (μ.cupC h (μ.cupMultiC a u) y) ∈ F^((a : ℤ) + q) H_dR^(m : ℤ)(X) :=
  spec_bettiDeRhamHQ_cupC_cupMultiC_mem_of_cupLeft_aux X hL h u hu q y hy

/-- With `CupFiltered X μ`, whose case `i = 1`, `p = 1` is `hL`: two holomorphic classes raise the
filtration by two. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hC : CupFiltered X μ) {k m : ℕ} (h : 2 + k = m)
    (u : Fin 2 → ℂ ⊗[ℚ] HQ X 1) (hu : ∀ i, bettiDeRhamHQ X 1 (u i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X))
    (q : ℤ) (y : ℂ ⊗[ℚ] HQ X k) (hy : bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X)) :
    bettiDeRhamHQ X m (μ.cupC h (μ.cupMultiC 2 u) y) ∈ F^(((2 : ℕ) : ℤ) + q) H_dR^(m : ℤ)(X) :=
  spec_bettiDeRhamHQ_cupC_cupMultiC_mem_of_cupLeft X
    (fun h q x y hx hy => hC.mem h 1 q x y hx hy) h u hu q y hy

/-- **Cup with too many holomorphic classes vanishes, from `hL`.** For abelian `X` and every cup
product `μ`: the implication from `hL` to `x ∪ (u_1 ∪ ⋯ ∪ u_a) = 0` whenever `β_n x ∈ F^p H^n`,
every `β_1 u_i ∈ F^1 H^1`, and `p + a > dim X`. By graded commutativity
(`CupProduct.graded_comm`, through the base change `cupC`) the product is `±(u_1 ∪ ⋯ ∪ u_a) ∪ x`,
whose image lies in `F^{a + p}` (`spec_bettiDeRhamHQ_cupC_cupMultiC_mem_of_cupLeft`), which is `0`
above the dimension in every degree (`spec_hodgeFiltration_eq_bot_of_dim_lt`); `bettiDeRhamHQ` is
injective for abelian `X` (`spec_bettiDeRhamIso_abelian`).
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1 and §8.3.1 (`Ω^q = 0` for
`q > dim X`); `spec_hodgeFiltration_eq_bot_of_dim_lt`, `CupProduct.graded_comm` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_cupC_cupMultiC_eq_zero_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {n a m : ℕ} (h : n + a = m) (p : ℤ) (x : ℂ ⊗[ℚ] HQ X n)
    (hx : bettiDeRhamHQ X n x ∈ F^p H_dR^(n : ℤ)(X)) (u : Fin a → ℂ ⊗[ℚ] HQ X 1)
    (hu : ∀ i, bettiDeRhamHQ X 1 (u i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X))
    (hpa : (dim X.left : ℤ) < p + a) :
    μ.cupC h x (μ.cupMultiC a u) = 0 :=
  spec_cupC_cupMultiC_eq_zero_of_cupLeft_aux X hL h p x hx u hu hpa

/-- Every class cups to zero with `dim X + 1` holomorphic classes (`p = 0`, `F^0` is everything). -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X}
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {n m : ℕ} (h : n + (dim X.left + 1) = m) (x : ℂ ⊗[ℚ] HQ X n)
    (u : Fin (dim X.left + 1) → ℂ ⊗[ℚ] HQ X 1)
    (hu : ∀ i, bettiDeRhamHQ X 1 (u i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) :
    μ.cupC h x (μ.cupMultiC (dim X.left + 1) u) = 0 :=
  spec_cupC_cupMultiC_eq_zero_of_cupLeft X hL h 0 x
    (by rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]; exact Submodule.mem_top) u hu
    (by push_cast; omega)

/-- **A filtered class cups to zero with a cup-wedge piece of high holomorphic type, from `hL`.**
For abelian `X` and a cup product `μ` with the torus theorem: the implication from `hL` to
`x ∪ y = 0` whenever `β_n x ∈ F^p H^n`, `β_j y ∈ W(a, j - a)` and `p + a > dim X`. This is the one
step of opp1's `spec_hodgeFiltration_le_iSup_cupWedgePiece` that used `CupFiltered`. `β_j` is
injective (`spec_bettiDeRhamIso_abelian`), so it suffices to take `y = cupMultiC j v` with
`v i ∈ cohomologyHodgePiece X 1 (d i)` and `∑ d i = (a, j - a)`. Types other than `(1, 0)` and
`(0, 1)` give `v i = 0` (`cohomologyHodgePiece_one_eq_bot`); otherwise exactly `a` factors have
type `(1, 0)`, hence lie in `F^1 H^1`. Reordering them to the front
(`spec_cupMultiC_comp_perm`) and splitting (`cupMultiC_append`) gives `y = ±U ∪ V`, and
`x ∪ (U ∪ V) = (x ∪ U) ∪ V = 0` (associativity, `spec_cupC_cupMultiC_eq_zero_of_cupLeft`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
`spec_cupC_cupMultiC_eq_zero_of_cupLeft`, `spec_cupMultiC_comp_perm` and `cupMultiC_append`. -/
theorem spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {n j m : ℕ} (h : n + j = m) (p a : ℤ) (x : ℂ ⊗[ℚ] HQ X n)
    (hx : bettiDeRhamHQ X n x ∈ F^p H_dR^(n : ℤ)(X)) (y : ℂ ⊗[ℚ] HQ X j)
    (hy : bettiDeRhamHQ X j y ∈ cupWedgePiece X μ j (a, (j : ℤ) - a))
    (hpa : (dim X.left : ℤ) < p + a) :
    μ.cupC h x y = 0 :=
  spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft_aux X hT hL h p a x hx y hy hpa

/-- A degree-one class in `F^1` cups to zero with every class of the cup-wedge piece
`W(g, j - g)`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {j m : ℕ} (h : 1 + j = m) (x : ℂ ⊗[ℚ] HQ X 1)
    (hx : bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) (y : ℂ ⊗[ℚ] HQ X j)
    (hy : bettiDeRhamHQ X j y ∈ cupWedgePiece X μ j (dim X.left, (j : ℤ) - dim X.left)) :
    μ.cupC h x y = 0 :=
  spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft X hT hL h 1 _ x hx y hy (by omega)

/-- **The upper bound from `hL`.** For abelian `X` of dimension `g` and a cup product `μ` with the
torus theorem: the implication from `hL` to `F^p H_dR^n(X) ≤ ⨆_{p' ≥ p} W(p', n - p')`. This is
opp1's `spec_hodgeFiltration_le_iSup_cupWedgePiece` with `hL` in place of `CupFiltered X μ`. For
`n > 2g` the space is `0`. Otherwise let `α = β x ∈ F^p H^n`, decompose it along the cup-wedge
pieces (`spec_cupWedgePiece_isInternal`), and fix `p' < p`. Every `y` in degree `2g - n` with
`β y ∈ W(g - p', ·)` has `x ∪ y = 0` (`spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft`, since
`p + g - p' > g`); this replaces opp1's use of `CupFiltered.mem`. The other components cup into
top-degree pieces of type `≠ (g, g)`, which vanish (`spec_cupC_mem_cupWedgePiece`,
`spec_cupWedgePiece_top_eq_bot`), so the type-`p'` component also cups to `0` with that piece, and
it is `0` by typed Poincaré duality (`spec_eq_zero_of_cupC_cupWedgePiece`). The rest of opp1's
proof is unchanged.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft`, `spec_cupWedgePiece_top_eq_bot` and
`spec_eq_zero_of_cupC_cupWedgePiece`. -/
theorem spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) ≤ ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') :=
  spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft_aux X hT hL n p

/-- With the instantiated cup product: `F^1 H^2` lies in the span of the cup-wedge pieces of first
index at least `1`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    F^1 H_dR^((2 : ℕ) : ℤ)(X) ≤
      ⨆ (p' : ℤ) (_ : 1 ≤ p'), cupWedgePiece X (cupProductOf X) 2 (p', ((2 : ℕ) : ℤ) - p') :=
  spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft X (torusCohomology_cupProductOf X) hL 2 1

/-- **Opposedness from `hL`.** For abelian `X` and a cup product `μ` with the torus theorem: the
implication from `hL` to `F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)`, for every `n` and `p`:
`spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft` and opp1's
`spec_opposed_of_hodgeFiltration_le`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft` and `spec_opposed_of_hodgeFiltration_le`. -/
theorem spec_opposed_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (p : ℤ) :
    hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ :=
  spec_opposed_of_cupLeft_aux X hT hL n p

/-- With cupf1's statement 12: the Hodge filtration is the filtration of the cup-wedge
decomposition, from `hL` alone. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) = ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') :=
  spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft X hT hL n
    (fun p _ _ => spec_opposed_of_cupLeft X hT hL n p) p

/-- **`CupFiltered` from `hL` alone.** For abelian `X` and a cup product `μ` with the torus
theorem: the implication from `hL` to `CupFiltered X μ`: cupf1's `spec_cupFiltered_of_cupLeft`
with its opposedness binder supplied by `spec_opposed_of_cupLeft`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1; `spec_cupFiltered_of_cupLeft`
and `spec_opposed_of_cupLeft`. -/
theorem spec_cupFiltered_of_cupLeft_alone (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    CupFiltered X μ :=
  spec_cupFiltered_of_cupLeft_alone_aux X hT hL

/-- With the instantiated cup product, the ledger hypothesis O5 follows from `hL`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    CupFiltered X (cupProductOf X) :=
  spec_cupFiltered_of_cupLeft_alone X (torusCohomology_cupProductOf X) hL

/-- **`HodgeDecomposition X` from `hL` alone.** For abelian `X` and a cup product `μ` with the
torus theorem: the implication from `hL` to `HodgeDecomposition X`: opp1's
`spec_hodgeDecomposition_of_cupFiltered` with `spec_cupFiltered_of_cupLeft_alone` (equivalently,
cupf1's `spec_hodgeDecomposition_of_cupLeft` with `spec_opposed_of_cupLeft`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1; Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_hodgeDecomposition_of_cupFiltered` and `spec_cupFiltered_of_cupLeft_alone`. -/
theorem spec_hodgeDecomposition_of_cupLeft_alone (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupLeft_alone_aux X hT hL

/-- **With the instantiated cup product, `hL` for `cupProductOf X` is the single open input for
`HodgeDecomposition X` on abelian `X`**: the torus theorem for `cupProductOf X` is proved
(`torusCohomology_cupProductOf`). -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X) hL

/-- **`CupFiltered` is equivalent to `hL`.** For abelian `X` and a cup product `μ` with the torus
theorem, `CupFiltered X μ` holds exactly when `hL` does. `→` is the case `i = 1`, `p = 1` of
`CupFiltered.mem` (cupf1's `example` after `spec_cupFiltered_of_cupLeft`); `←` is
`spec_cupFiltered_of_cupLeft_alone`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1; `CupFiltered.mem` and
`spec_cupFiltered_of_cupLeft_alone`. -/
theorem spec_cupFiltered_iff_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) :
    CupFiltered X μ ↔
      ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
        bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
        bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
        bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X) :=
  spec_cupFiltered_iff_cupLeft_aux X hT

/-- So the ledger hypothesis `CupFiltered X (cupProductOf X)` (O5) and `hL` for `cupProductOf X`
are interchangeable on abelian `X`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hC : CupFiltered X (cupProductOf X)) {k m : ℕ} (h : 1 + k = m) (q : ℤ)
    (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k) (hx : bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X))
    (hy : bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X)) :
    bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X) :=
  (spec_cupFiltered_iff_cupLeft X (torusCohomology_cupProductOf X)).mp hC h q x y hx hy

end HodgeLean.Adapters
