import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapProjection

/-! # Vanishing of actual triad projections on an open cover -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- On an actual two-open cover the original sum-relative triad projection is zero on homology.
Source: Hatcher, Algebraic Topology, section 2.2, subdivision and excision for open covers.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_projection_zero_of_open_cover
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : ℕ) (c : Homology ℚ X n) :
    (HomologicalComplex.homologyMap (triadRelativeChainProjection ℚ X A B) n).hom c = 0 := by
  let P := TopPair.ofSubset (X := X) (A ∪ B)
  have hmap : IsIso P.map := by
    change IsIso (TopPair.ofSubset (X := X) (A ∪ B)).map
    rw [hcover]
    exact (TopCat.isIso_iff_isHomeomorph _).mpr (Homeomorph.Set.univ X).isHomeomorph
  have hchain : IsIso ((chainPairFunctor ℚ).obj P).hom := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map P.map)
    infer_instance
  have hK : CategoryTheory.Limits.IsZero ((relativeChainFunctor ℚ).obj P) :=
    CategoryTheory.Limits.isZero_cokernel_of_epi ((chainPairFunctor ℚ).obj P).hom
  have hH : CategoryTheory.Limits.IsZero (RelativeHomology ℚ P n) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).map_isZero hK
  letI : Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ B)) n) :=
    ModuleCat.subsingleton_of_isZero hH
  letI : QuasiIso (triadToUnionRelativeChainMap ℚ X A B) :=
    triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hA hB
  apply (isoOfQuasiIsoAt (triadToUnionRelativeChainMap ℚ X A B) n).toLinearEquiv.injective
  change (_ : RelativeHomology ℚ P n) = _
  exact Subsingleton.elim _ _

/-- A cocycle supported away from the first open has a cap class with zero original relative projection modulo the second open of a cover.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, excision and relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_projection_zero_of_open_cover
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
        change AlgebraicTopology.Simplicial.coboundary ℚ p
          (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ) = 0
        rw [← relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ, hφ, map_zero]⟩
    ∀ c : Homology ℚ X (p + q),
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
        (capHomologyMap ℚ X p q ψ c) = 0 := by
  dsimp only
  intro c
  have h := properCycle_cap_relative_projection_on_cocycle X A B p q φ hφ c
  exact h.trans (by rw [properCycle_triad_projection_zero_of_open_cover X A B hA hB hcover,
    map_zero])

end HodgeLean.Foundations.QuotientDuality
