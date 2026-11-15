import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadCapChain

/-! # The actual relative-to-triad cap square on original homology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Projecting the original relative cap class modulo the second subspace is the original triad cap on its literal quotient homology class.
Source: properCycle_relative_triad_cap_chain_square; functoriality of short-complex homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triad_cap_homology
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) (p+q)) :
    (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
      (relativeCapHomologyMap ℚ (TopPair.ofSubset (X := X) A) p q φ hφ c) =
      triadCapHomologyMap ℚ X A B p q φ hφ
        ((HomologicalComplex.homologyMap (properCycle_relative_to_triad_chain_map X A B)
          (p+q)).hom c) := by
  let PN := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (p+q)).map
    (properCycle_relative_to_triad_chain_map X A B)
  let PB := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B))
  let F := relativeCapShortComplexHom ℚ (TopPair.ofSubset (X := X) A) p q φ hφ
  let G := triadCapShortComplexHom ℚ X A B p q φ hφ
  have hh : ShortComplex.homologyMap (F ≫ PB) = ShortComplex.homologyMap (PN ≫ G) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change F.τ₂ ≫ PB.τ₂ = PN.τ₂ ≫ G.τ₂
    rw [relativeCapShortComplexHom_τ₂, triadCapShortComplexHom_τ₂]
    exact properCycle_relative_triad_cap_chain_square X A B p q φ
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh c

end HodgeLean.Foundations.QuotientDuality
