import HodgeLean.RealDefs.Operations

/-! # The Hodge conjecture in dimension at most three

Against the pinned definitions of `HodgeConjecture`, this file proves upstream's
`HodgeConjectureInDimensionLE 3` (`hodgeConjectureInDimensionLE_three`) and its abelian-variety
case (`hodgeConjectureForAbelianVarietiesInDimensionLE_three`) from:

* Lefschetz (1,1) (`LefschetzOneOneHyp`) and the preconnectedness of `X(ℂ)`
  (`ComplexPointsPreconnected`, which gives degree zero through `hodge_degree_zero`);
* for each `X` of dimension at most three, a cup product `μ` and a class `η ∈ H^2` satisfying
  Hard Lefschetz (`HardLefschetz`, roadmap `docs/roadmap/layer3.md` §3 O3), divisor closure
  (`AlgebraicTimesDivisor`, O6) and Hodge reflection (`LefschetzReflectsHodge`, O4);
* vanishing of `H^m(X(ℂ); ℚ)` above `m = 2 · dim X` (`VanishingAboveTop`, O7).

The proof is roadmap §2(a). With `n = dim X ≤ 3`, degree `p = 0` is `hodge_degree_zero`, `p = 1` is
Lefschetz (1,1), and `p > n` is vanishing. The remaining cases `(n, p) ∈ {(2,2), (3,2), (3,3)}`
use the Hard Lefschetz bijection `L^r : H^(2j) → H^(2p)` with `j = n − p ∈ {0, 1}` and
`r = 2p − n`: a Hodge class `b = L^r a` has `a` Hodge by reflection, so `a` is algebraic by degree
zero or Lefschetz (1,1), and `b` is algebraic by divisor closure applied `r` times
(`lefschetzPow_mem_algebraicCycleClassSpan`).

The structures are stated over `HQ X n` (`Operations`), for the kernel-time reason recorded
there; `HQ X n` is upstream's `H^n(X; ℚ)` by definition (`HQ_def`). -/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLean.RealDefs

/-- The Lefschetz (1,1) theorem, upstream's `LefschetzOneOne`, as a hypothesis: every rational
Hodge class of degree two on a smooth projective complex variety is the class of a divisor.

Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (the Lefschetz theorem on (1,1)-classes).

The brief cites page 163 for the theorem; that page number was not checked against a copy here,
so only the chapter and section are pinned.

**Consistency.** For `X = ℙ¹`, `H^2(X(ℂ); ℚ) = ℚ` is spanned by the class of a point, which is
algebraic (a codimension-one cycle), so every class in `H^2`, Hodge or not, is in the span of
divisor classes. This is expected, not proved here for upstream's definitions. -/
@[hodge_hypothesis]
structure LefschetzOneOneHyp : Prop where
  holds : LefschetzOneOne

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Hard Lefschetz for the cup product `μ` and the class `η ∈ H^2`: for `k ≤ n = dim X`, the
Lefschetz power `L^(n−k) = (η ∪ -)^(n−k) : H^k(X(ℂ); ℚ) → H^(2n−k)(X(ℂ); ℚ)` is bijective.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, Theorem 6.25 (hard Lefschetz, for the class of a Kähler form).

Voisin states the theorem over `ℝ` for the class of a Kähler form; for `η` the class of an ample
divisor (a rational class), bijectivity over `ℚ` follows by base change `ℚ → ℝ`, which this
structure takes as part of the hypothesis. The structure does not say that `η` is ample: any `η`
with bijective Lefschetz powers is an instance.

**Consistency.** For `X = ℙ¹` (`n = 1`), take `η` the class of a point. At `k = 0`,
`L : H^0 → H^2` sends `1` to `[pt]`, a bijection `ℚ → ℚ`; at `k = 1`, `L^0` is the identity of
`H^1 = 0`. This assumes the cup product on `ℙ¹` exists as a `CupProduct` instance. Its normalisation
`[ℙ¹] = 1` holds (`cycleComponentSheafClass_generic`), but no instance is constructed.

**Non-degeneracy.** At `k = 0`, `L^n : H^0 → H^(2n)` is bijective, and `H^0 ≠ 0` for any `μ`
(`CupProduct.unitClass_ne_zero`), so `η = 0` is no instance when `n ≥ 1`. -/
@[hodge_hypothesis]
structure HardLefschetz (μ : CupProduct X) (η : HQ X 2) : Prop where
  bijective : ∀ {k m : ℕ} (_hk : k ≤ dim X.left) (h : k + 2 * (dim X.left - k) = m),
      Function.Bijective (lefschetzPow X μ η (dim X.left - k) h)

/-- Divisor closure for `μ` and `η`: `η` is the class of a divisor (a rational combination of
codimension-one cycle classes), and cup product with `η` maps the codimension-`p` cycle classes
into the codimension-`(p + 1)` ones.

Source: Fulton, *Intersection Theory*, 2nd ed., Ch. 19, Corollary 19.2 (the cycle map is a ring homomorphism), with Bertini for a general hyperplane section (Hartshorne, *Algebraic Geometry*, Thm II.8.18).

For `η` the class of a hyperplane section `H`, the cycle map takes the intersection `H · Z` to
`η ∪ [Z]`, and `H · Z` is a codimension-`(p + 1)` cycle; `H` meets `Z` properly once it contains
no component of `Z`, and Bertini (Hartshorne II.8.18) additionally makes a general `H` smooth. Upstream's cycle classes (`cycleComponentSheafClass`) are not proved to agree with
Fulton's cycle map; this structure takes the agreement as part of the hypothesis.

**Consistency.** For `X = ℙ¹`, take `η = [pt]`, the class of a closed point, so `η_mem` holds.
For `p = 0`, every class in `H^0` is a rational multiple of `[ℙ¹]`, and `η ∪ q[ℙ¹] = q[pt]` is
in the span of codimension-one classes; for `p ≥ 1`, the target `H^(2p+2)` is `0`. -/
@[hodge_hypothesis]
structure AlgebraicTimesDivisor (μ : CupProduct X) (η : HQ X 2) : Prop where
  η_mem : η ∈ algebraicCycleClassSpan X 1
  cup_mem : ∀ {p : ℕ} (h : 2 + 2 * p = 2 * (p + 1)) (a : HQ X (2 * p)),
      a ∈ algebraicCycleClassSpan X p → μ.cup h η a ∈ algebraicCycleClassSpan X (p + 1)

/-- Vanishing above the top degree: `H^m(X(ℂ); ℚ) = 0` for `m > 2 · dim X`.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, Ch. II §16 (cohomological dimension: sheaf cohomology of a topological `d`-manifold vanishes above degree `d`), section only.

It is applied with `d = dim_ℝ X(ℂ) = 2 · dim X`, since `X(ℂ)` is a complex manifold of complex
dimension `dim X`. Neither that dimension count nor the manifold structure of `X(ℂ)` is linked
to upstream's `dim X.left` here; the structure takes the conclusion as the hypothesis.

**Consistency.** For `X = ℙ¹`, `X(ℂ)` is the 2-sphere, whose rational cohomology vanishes above
degree `2 = 2 · dim ℙ¹`. -/
@[hodge_hypothesis]
structure VanishingAboveTop : Prop where
  subsingleton : ∀ m : ℕ, 2 * dim X.left < m → Subsingleton (HQ X m)

/-- Hodge reflection for `μ` and `η`: for `a ∈ H^(2p)` with `2p + r = n = dim X`, if `L^r a` is a
Hodge class, so is `a`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, Ch. 6 §6.2 (the Lefschetz operator of a Kähler class, of type (1,1)) and §7.3.1, p. 174 (morphisms of Hodge structures and their strictness); §6.2 section only.

It bundles two facts:
* `L = η ∪ -` is a morphism of Hodge structures of type `(1, 1)` when `η` is a Hodge class of
  degree two (cup product respects the Hodge filtration and conjugation), so `L^r` is one of
  type `(r, r)`;
* a morphism of Hodge structures is strict, so a class whose image is of type `(m, m)` differs
  from a class of type `(p, p)` by an element of the kernel; with `L^r` injective on `H^(2p)`,
  `a` itself is a Hodge class.

**Range.** Reflection is asserted only for `2p + r = n`, the field's hypothesis `_hr`, which is
the one case the proof of `hodgeConjectureInDimensionLE_three` uses. There
`L^r = L^(n−2p) : H^(2p) → H^(2n−2p)` is the Hard Lefschetz bijection, so the field follows from
`L^r` being a morphism of Hodge structures of type `(r, r)` applied to the inverse bijection.
Without a range restriction it is false: on a K3 or abelian surface (`n = 2`, `h^(2,0) > 0`) with
`p = 1` and `r = 2`, `L^2 : H^2 → H^6 = 0` sends every `a` to `0 ∈ Hdg^3`, and an unrestricted
field would make every class in `H^2` a Hodge class.

Neither fact is pinned to a theorem number. This structure is derived, with no Tate twist, by
`lefschetzReflectsHodge_of_cupFiltered` (`CupFiltered.lean`) from the Betti–de Rham comparison
(C2), the Hodge decomposition (C4), the cup product respecting the Hodge filtration (O5,
`CupFiltered`), Hard Lefschetz and `η ∈ Hdg^1`; `hodgeConjectureInDimensionLE_three_of_cupFiltered`
restates the milestone over those hypotheses.

**Consistency.** For `X = ℙ¹`, every class in `H^0` is in `Hdg^0` and every class in `H^2` is in
`Hdg^1` (both are spanned by algebraic classes of type `(0,0)` and `(1,1)`), and `H^(2p) = 0` for
`p ≥ 2`, so every `a ∈ H^(2p)` is a Hodge class and the implication holds. -/
@[hodge_hypothesis]
structure LefschetzReflectsHodge (μ : CupProduct X) (η : HQ X 2) : Prop where
  reflects : ∀ {p r m : ℕ} (h : 2 * p + 2 * r = 2 * m) (_hr : 2 * p + r = dim X.left)
      (a : HQ X (2 * p)),
      lefschetzPow X μ η r h a ∈ Hdg^m(X; ℚ) → a ∈ Hdg^p(X; ℚ)

variable {X}

/-- One step of the Lefschetz power, with the indices given by equations. -/
theorem lefschetzPow_succ (μ : CupProduct X) (η : HQ X 2) (r : ℕ) {k m' m : ℕ}
    (h : k + 2 * (r + 1) = m) (h' : k + 2 * r = m') (h'' : 2 + m' = m) (a : HQ X k) :
    lefschetzPow X μ η (r + 1) h a = μ.cup h'' η (lefschetzPow X μ η r h' a) := by
  subst h h'
  rfl

/-- The zeroth Lefschetz power is the identity. -/
theorem lefschetzPow_zero (μ : CupProduct X) (η : HQ X 2) {k : ℕ} (h : k + 2 * 0 = k)
    (a : HQ X k) : lefschetzPow X μ η 0 h a = a :=
  rfl

/-- Divisor closure, iterated: `L^r` maps codimension-`p` cycle classes into codimension-`q`
ones, where `p + r = q`. -/
theorem lefschetzPow_mem_algebraicCycleClassSpan {μ : CupProduct X} {η : HQ X 2}
    (hD : AlgebraicTimesDivisor X μ η) :
    ∀ (r p q : ℕ) (h : 2 * p + 2 * r = 2 * q) (a : HQ X (2 * p)),
      a ∈ algebraicCycleClassSpan X p → lefschetzPow X μ η r h a ∈ algebraicCycleClassSpan X q
  | 0, p, q, h, a, ha => by
    obtain rfl : q = p := by omega
    rwa [lefschetzPow_zero]
  | r + 1, p, q, h, a, ha => by
    obtain rfl : q = p + r + 1 := by omega
    rw [lefschetzPow_succ μ η r h (m' := 2 * (p + r)) (by ring) (by ring)]
    exact hD.cup_mem _ _ (lefschetzPow_mem_algebraicCycleClassSpan hD r p (p + r) (by ring) a ha)

/-- **The Hodge conjecture in dimension at most three**, upstream's `HodgeConjectureInDimensionLE 3`,
from Lefschetz (1,1), the preconnectedness of `X(ℂ)` (degree zero), and, for each `X` of dimension
at most three, a cup product `μ` with a class `η ∈ H^2` satisfying Hard Lefschetz, divisor closure
and Hodge reflection, plus vanishing above the top degree.

Source: Lewis, *A Survey of the Hodge Conjecture*, 2nd ed., CRM Monograph Ser. 10, the argument that Lefschetz (1,1) and hard Lefschetz give the conjecture in dimension at most three, section-level; proof shape from `docs/roadmap/layer3.md` §2(a).

The statement is the brief's, binder for binder; no binder form had to change.

**U3 (closed, `docs/notes/fundamental-class-unit.md`).** `CupProduct X` requires the class of
`X` (upstream's `cycleComponentSheafClass` of the generic point) to equal the unit `unitClass X`
(`CupProduct.fundamentalClass_eq_unit`). That holds for every eligible `X`
(`cycleComponentSheafClass_generic`, in `FundamentalClassUnit.lean`), so `hops` is not vacuous on
this account.

Checks: F-1663 -/
@[hodge_milestone] theorem hodgeConjectureInDimensionLE_three
    (h11 : LefschetzOneOneHyp) (hconn : ComplexPointsPreconnected)
    (hops : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      dim X.left ≤ 3 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ LefschetzReflectsHodge X μ η)
    (hvan : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      VanishingAboveTop X) :
    HodgeConjectureInDimensionLE 3 := by
  intro X _ _ _ hX p b hb
  have low : ∀ j, j ≤ 1 → Hdg^j(X; ℚ) ≤ algebraicCycleClassSpan X j := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact hodge_degree_zero hconn X
    · exact h11.holds X
  by_cases hp1 : p ≤ 1
  · exact low p hp1 hb
  by_cases hpn : dim X.left < p
  · have := (hvan X).subsingleton (2 * p) (by omega)
    obtain rfl : b = 0 := Subsingleton.elim (α := HQ X (2 * p)) b 0
    exact Submodule.zero_mem _
  obtain ⟨μ, η, hL, hD, hR⟩ := hops X hX
  obtain ⟨j, hj⟩ : ∃ j, j = dim X.left - p := ⟨_, rfl⟩
  have hk : 2 * j ≤ dim X.left := by omega
  have h : 2 * j + 2 * (dim X.left - 2 * j) = 2 * p := by omega
  obtain ⟨a, rfl⟩ := (hL.bijective hk h).2 b
  have ha : a ∈ Hdg^j(X; ℚ) := hR.reflects h (by omega) a hb
  exact lefschetzPow_mem_algebraicCycleClassSpan hD _ j p h a (low j (by omega) ha)

-- The conclusion of `hodgeConjectureInDimensionLE_three` is upstream's constant
-- `HodgeConjectureInDimensionLE 3` itself (`HodgeConjecture/Variants.lean`), not a restatement.

/-- **The Hodge conjecture for abelian varieties of dimension at most three**, upstream's
`HodgeConjectureForAbelianVarietiesInDimensionLE 3`, under the hypotheses of
`hodgeConjectureInDimensionLE_three`, through
`hodgeConjectureForAbelianVarietiesInDimensionLE_of_inDimensionLE`.

Source: Lewis, *A Survey of the Hodge Conjecture*, 2nd ed., CRM Monograph Ser. 10, the dimension-at-most-three case, section-level; an abelian variety is a smooth projective variety.

U3 is closed as for `hodgeConjectureInDimensionLE_three`: `[X] = 1` holds for every eligible `X`
(`cycleComponentSheafClass_generic`), so `hops` is not vacuous on that account. No `CupProduct`
instance is constructed.

Checks: F-1663 -/
@[hodge_milestone] theorem hodgeConjectureForAbelianVarietiesInDimensionLE_three
    (h11 : LefschetzOneOneHyp) (hconn : ComplexPointsPreconnected)
    (hops : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      dim X.left ≤ 3 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ LefschetzReflectsHodge X μ η)
    (hvan : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      VanishingAboveTop X) :
    HodgeConjectureForAbelianVarietiesInDimensionLE 3 :=
  hodgeConjectureForAbelianVarietiesInDimensionLE_of_inDimensionLE
    (hodgeConjectureInDimensionLE_three h11 hconn hops hvan)

end HodgeLean.RealDefs
