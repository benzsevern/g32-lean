import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing

/-! # The original cap map and the actual same-pair relative cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Capping the projected relative homology class agrees with the original absolute cap of the pulled-back relative cocycle.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products and triads.
HC no distance; AV milestone no distance. -/
lemma properCycle_same_pair_cap_projection_on_cocycle
    (P : TopPair.{0}) (p q : ℕ)
    (φ : RelativeCochain ℚ P p)
    (hφ : relativeCoboundary ℚ P p φ = 0) :
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj P.fst) p :=
      ⟨relativeCochainToAbsolute ℚ P p φ, by
        change AlgebraicTopology.Simplicial.coboundary ℚ p
          (relativeCochainToAbsolute ℚ P p φ) = 0
        rw [← relativeCochainToAbsolute_coboundary ℚ P p φ, hφ, map_zero]⟩
    ∀ c : Homology ℚ P.fst (p + q),
      capHomologyMap ℚ P.fst p q ψ c =
        relativeCapHomologyMap ℚ P p q φ hφ
          ((relativeHomologyProjection ℚ P (p + q)).hom c) := by
  let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj P.fst) p :=
    ⟨relativeCochainToAbsolute ℚ P p φ, by
      change AlgebraicTopology.Simplicial.coboundary ℚ p
        (relativeCochainToAbsolute ℚ P p φ) = 0
      rw [← relativeCochainToAbsolute_coboundary ℚ P p φ, hφ, map_zero]⟩
  dsimp only
  intro c
  let PN := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (p + q)).map
    (relativeChainProjection ℚ P)
  let F := AlgebraicTopology.Simplicial.capShortComplexHom ℚ p q ψ.1 ψ.2
  let G := relativeCapShortComplexHom ℚ P p q φ hφ
  have hh : ShortComplex.homologyMap (PN ≫ G) = ShortComplex.homologyMap F := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change (relativeChainProjection ℚ P).f (p + q) ≫ G.τ₂ =
      F.τ₂
    rw [relativeCapShortComplexHom_τ₂, AlgebraicTopology.Simplicial.capShortComplexHom_τ₂,
      relativeChainProjection_relativeCapHom]
    rfl
  rw [ShortComplex.homologyMap_comp] at hh
  exact (ConcreteCategory.congr_hom hh c).symm

end HodgeLean.Foundations.QuotientDuality
