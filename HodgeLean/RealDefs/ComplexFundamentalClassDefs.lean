import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClass
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.EuclideanNeighborhoodOrientation

/-! # Local homology along a subset: the predicates of Hatcher's Lemma 3.27

For a space `M`, a subset `A` and a degree `i`, the local homology of `M` along `A` is upstream's
`RelativeHomology ℚ (TopPair.ofSubset Aᶜ) i`, that is `H_i(M, M \ A; ℚ)`. For `B ⊆ A` the
restriction `H_i(M, M \ A) → H_i(M, M \ B)` is `relativeHomologyMap` of upstream's
`supportInclusionPairMap`. This file names three properties of a subset that Hatcher's
Lemma 3.27 is about, and the family of translates of upstream's `standardComplexLocalClass` on
`Fin d → ℂ` used by the falsification check. It introduces no new homology theory and no
hypothesis.
-/

open TopologicalSpace AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

variable (M : Type) [TopologicalSpace M] (n : ℕ)

/-- Local homology of `M` along `A` vanishes in every degree above `n`.
Source: Hatcher, *Algebraic Topology*, Lemma 3.27(b). -/
def LocalHomologyVanishesAbove (A : Set M) : Prop :=
  ∀ i, n < i → Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i)

example : LocalHomologyVanishesAbove M n (∅ : Set M) ↔
    ∀ i, n < i → Subsingleton
      (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ) i) :=
  Iff.rfl

/-- A class in `H_n(M, M \ A; ℚ)` is zero when all of its restrictions to points of `A` are
zero. This is the uniqueness half of Hatcher's Lemma 3.27(a).
Source: Hatcher, *Algebraic Topology*, Lemma 3.27(a). -/
def LocalHomologyDetectedByPoints (A : Set M) : Prop :=
  ∀ α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
    (∀ (x : M) (hx : x ∈ A),
      relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) →
      α = 0

example (A : Set M) (h : LocalHomologyDetectedByPoints M n A)
    (α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n)
    (hα : ∀ (x : M) (hx : x ∈ A),
      relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) :
    α = 0 :=
  h α hα

/-- Some class in `H_n(M, M \ A; ℚ)` restricts to `μ x` at every point `x` of `A`. This is the
existence half of Hatcher's Lemma 3.27(a), for the family of local classes `μ`.
Source: Hatcher, *Algebraic Topology*, Lemma 3.27(a). -/
def HasClassAlong (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n) (A : Set M) :
    Prop :=
  ∃ α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
    ∀ (x : M) (hx : x ∈ A),
      relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = μ x

example (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n) :
    HasClassAlong M n μ ∅ :=
  ⟨0, fun _ hx => absurd hx (Set.notMem_empty _)⟩

/-- The local class at `v` of `Fin d → ℂ`: upstream's `standardComplexLocalClass` at the origin,
moved to `v` by the translation `w ↦ w + v` as a map of pairs `(E, E \ 0) → (E, E \ v)`.
Source: Hatcher, *Algebraic Topology*, §3.3, p. 234 (a local orientation of `ℝⁿ` at each point,
carried by translation); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §4. -/
noncomputable def translatedStandardComplexLocalClass (d : ℕ) (v : Fin d → ℂ) :
    RelativeHomology ℚ (pointComplementPair v) (2 * d) :=
  relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) v)
    (standardComplexLocalClass ℚ d)

example (d : ℕ) : translatedStandardComplexLocalClass d 0 =
    relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) 0)
      (standardComplexLocalClass ℚ d) :=
  rfl

end HodgeLean.RealDefs
