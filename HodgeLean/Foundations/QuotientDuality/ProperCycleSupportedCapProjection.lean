import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Excision.Triad
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing

/-! # The original cap map and literal projection to a support-neighborhood pair -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Projecting the original cap class relative to the second triad subspace agrees with the actual sum-relative triad cap map.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products and triads.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_relative_projection_on_cocycle
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
        change AlgebraicTopology.Simplicial.coboundary ℚ p
          (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ) = 0
        rw [← relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ, hφ, map_zero]⟩
    ∀ c : Homology ℚ X (p + q),
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) q).hom
          (capHomologyMap ℚ X p q ψ c) =
        triadCapHomologyMap ℚ X A B p q φ hφ
          ((HomologicalComplex.homologyMap (triadRelativeChainProjection ℚ X A B) (p + q)).hom c) := by
  let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
    ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
      change AlgebraicTopology.Simplicial.coboundary ℚ p
        (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ) = 0
      rw [← relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ, hφ, map_zero]⟩
  dsimp only
  intro c
  let PN := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (p + q)).map
    (triadRelativeChainProjection ℚ X A B)
  let PB := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B))
  let F := AlgebraicTopology.Simplicial.capShortComplexHom ℚ p q ψ.1 ψ.2
  let G := triadCapShortComplexHom ℚ X A B p q φ hφ
  have hh : ShortComplex.homologyMap (PN ≫ G) = ShortComplex.homologyMap (F ≫ PB) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change (triadRelativeChainProjection ℚ X A B).f (p + q) ≫ G.τ₂ =
      F.τ₂ ≫ (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B)).f q
    rw [triadCapShortComplexHom_τ₂, AlgebraicTopology.Simplicial.capShortComplexHom_τ₂,
      triadRelativeChainProjection_triadCapHom]
    rfl
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  exact (ConcreteCategory.congr_hom hh c).symm

end HodgeLean.Foundations.QuotientDuality
