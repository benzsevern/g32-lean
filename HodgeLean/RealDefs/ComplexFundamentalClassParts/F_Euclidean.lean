import HodgeLean.RealDefs.ComplexFundamentalClassDefs
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Contractible
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter

/-! # Lane F helpers: Euclidean space has no fundamental class; translated local classes

Three facts about a finite-dimensional real normed space `E` used by the falsification check of
the fundamental-class spec:

* `H_n(E, ∅; ℚ)` vanishes for `n ≥ 1`, because the pair has empty subspace (so relative chains are
  absolute chains) and `E` is contractible;
* translation `w ↦ w + v` is an isomorphism of pairs `(E, E \ 0) ≅ (E, E \ v)`, so its homology
  map is injective;
* on a convex set containing the origin, a class restricting to a local class at the origin
  restricts at every other point to the translate of that local class.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

section Empty

variable (M : Type) [TopologicalSpace M]

lemma F_chainPairFunctor_hom_eq_zero_of_isEmpty (S : Set M) (hS : IsEmpty S) :
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) S)).hom = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro σ
  let f := ((TopPair.ofSubset (X := TopCat.of M) S).snd.toSSetObjEquiv _) σ
  exact (hS.false (f Convexity.StdSimplex.barycenter)).elim

lemma F_relativeChainProjection_isIso_of_isEmpty (S : Set M) (hS : IsEmpty S) :
    IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) S)) :=
  cokernel.π_of_zero (F_chainPairFunctor_hom_eq_zero_of_isEmpty M S hS)

/-- For a contractible space and a pair with empty subspace, relative homology vanishes in
positive degrees. -/
lemma F_relativeHomology_subsingleton_of_contractible [ContractibleSpace M] (S : Set M)
    (hS : IsEmpty S) (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) S) n) := by
  have := F_relativeChainProjection_isIso_of_isEmpty M S hS
  have hex := AlgebraicTopology.singularChainComplex_exactAt_of_contractible ℚ M n hn
  have hex' : ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) S)).ExactAt n :=
    (exactAt_iff_of_quasiIsoAt
      (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) S)) n).mp hex
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hex'
  exact ModuleCat.subsingleton_of_isZero hex'

end Empty

/-- On a finite-dimensional real normed space of positive dimension, the zero class is the only
class of `H_n(E, ∅; ℚ)`, so a family of point values with a nonzero member has no class. -/
theorem F_not_exists_fundamentalClass_euclidean {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (hpos : 0 < n)
    (μ : ∀ x : E, RelativeHomology ℚ (pointComplementPair x) n) (hμ : ∃ x : E, μ x ≠ 0) :
    ¬ ∃ w : RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens E) : Set E)ᶜ : Set (TopCat.of E))) n,
      ∀ y : E,
        relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of E)
              (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w = μ y := by
  rintro ⟨w, hw⟩
  obtain ⟨x, hx⟩ := hμ
  have hempty : IsEmpty (((⊤ : Opens E) : Set E)ᶜ : Set E) :=
    ⟨fun y => y.2 (Opens.mem_top y.1)⟩
  have := F_relativeHomology_subsingleton_of_contractible E _ hempty n hpos.ne'
  apply hx
  rw [← hw x, Subsingleton.elim w 0, map_zero]

section Translation

variable (E : Type) [NormedAddCommGroup E]

/-- Translation by `v` as an isomorphism of pairs `(E, E \ 0) ≅ (E, E \ v)`.
Source: Hatcher, *Algebraic Topology*, §3.3, p. 234 (local orientations of `ℝⁿ` carried by
translation). -/
def F_translationPointComplementPairIso (v : E) :
    TopPair.ofSubset (X := TopCat.of E) ({0}ᶜ : Set E) ≅
      TopPair.ofSubset (X := TopCat.of E) ({v}ᶜ : Set E) :=
  TopPair.isoOfSubset (Homeomorph.addRight v) fun x => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Homeomorph.coe_addRight,
      add_eq_right]

lemma F_translationPointComplementPairIso_hom (v : E) :
    (F_translationPointComplementPairIso E v).hom = translationPointComplementPairMap E v := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext a; rfl
  · ext x; rfl

example (v : E) :
    (F_translationPointComplementPairIso E v).hom ≫ (F_translationPointComplementPairIso E v).inv =
      𝟙 _ :=
  Iso.hom_inv_id _

lemma F_translationPointComplementPairMap_injective (v : E) (n : ℕ) :
    Function.Injective (relativeHomologyMap ℚ n (translationPointComplementPairMap E v)) := by
  intro a b hab
  have h := congrArg (relativeHomologyMap ℚ n (F_translationPointComplementPairIso E v).inv) hab
  rw [← F_translationPointComplementPairIso_hom] at h
  simpa only [← LinearMap.comp_apply, ← relativeHomologyMap_comp, Iso.hom_inv_id,
    relativeHomologyMap_id, LinearMap.id_apply] using h

end Translation

theorem F_translatedStandardComplexLocalClass_ne_zero (d : ℕ) (v : Fin d → ℂ) :
    translatedStandardComplexLocalClass d v ≠ 0 := by
  intro h
  have hne : standardComplexLocalClass ℚ d ≠ 0 := by
    rw [standardComplexLocalClass_ne_zero_iff]
    by_cases hd : d = 0
    · subst d
      exact standardLocalClass_zero_ne_zero
    · exact standardLocalClass_ne_zero_of_pos (d * 2) (Nat.mul_pos (Nat.pos_of_ne_zero hd) two_pos)
  apply hne
  apply F_translationPointComplementPairMap_injective (Fin d → ℂ) v (2 * d)
  rw [map_zero]
  exact h

/-- A class over a convex set containing the origin whose restriction to the origin is the
standard complex local class restricts at every point of the set to the translated class. -/
theorem F_restrict_eq_translated_of_convex (d : ℕ) {U : Set (Fin d → ℂ)}
    (h0 : (0 : Fin d → ℂ) ∈ U) (hU : Convex ℝ U)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) Uᶜ) (2 * d))
    (hc : relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (Fin d → ℂ)) (Set.singleton_subset_iff.mpr h0)) c =
        standardComplexLocalClass ℚ d)
    (y : Fin d → ℂ) (hy : y ∈ U) :
    relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (Fin d → ℂ)) (Set.singleton_subset_iff.mpr hy)) c =
        translatedStandardComplexLocalClass d y := by
  have h := (convexSupportTranslationPairHomotopy (Fin d → ℂ) U h0 hU y hy).relativeHomologyMap_apply_eq
    (R := ℚ) (2 * d) c
  rw [h, relativeHomologyMap_comp, LinearMap.comp_apply, hc]
  rfl

end HodgeLean.RealDefs
