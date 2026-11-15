import HodgeLean.Foundations.QuotientDuality.RetainedCycleRelativeChainCoordinates

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluation of an actual singular simplex at a specified actual simplex point. -/
def retainedSimplexAt (X : TopCat.{0}) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (t : SimplexCategory.toTop.{0}.obj ⦋n⦌) : X :=
  (TopCat.Hom.hom (show SimplexCategory.toTop.{0}.obj ⦋n⦌ ⟶ X from σ.down)) t

/-- A simplex cannot come from the complement of one of its actual image points. -/
theorem retained_simplex_not_from_point_complement (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (t : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    ∀ τ : (TopCat.toSSet.obj (pointComplementPair (retainedSimplexAt X n σ t)).snd) _⦋n⦌,
      (TopCat.toSSet.map (pointComplementPair (retainedSimplexAt X n σ t)).map).app (op ⦋n⦌) τ ≠ σ := by
  intro τ he
  have hv := congrArg (fun f : (TopCat.toSSet.obj X) _⦋n⦌ => retainedSimplexAt X n f t) he
  let v : {y : X // y ∈ ({retainedSimplexAt X n σ t}ᶜ : Set X)} :=
    retainedSimplexAt (pointComplementPair (retainedSimplexAt X n σ t)).snd n τ t
  change v.val = retainedSimplexAt X n σ t at hv
  exact v.property (Set.mem_singleton_iff.mpr hv)

/-- The actual point-complement relative-chain projections jointly detect every singular chain. -/
theorem retained_chain_eq_zero_of_point_projections (X : TopCat.{0}) (n : ℕ)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n)
    (hc : ∀ x : X, ((relativeChainProjection ℚ (pointComplementPair x)).f n).hom c = 0) :
    c = 0 := by
  classical
  apply (retainedChainCoordinateEquiv (TopCat.toSSet.obj X) n).injective
  change retainedChainCoordinates (TopCat.toSSet.obj X) n c =
    retainedChainCoordinates (TopCat.toSSet.obj X) n 0
  rw [map_zero]
  ext σ
  let t : SimplexCategory.toTop.{0}.obj ⦋n⦌ := Classical.choice inferInstance
  let x := retainedSimplexAt X n σ t
  have hσ := retained_simplex_not_from_point_complement X n σ t
  have hπ := ConcreteCategory.congr_hom
    (retained_relative_simplex_coordinate_projection (pointComplementPair x) n σ hσ) c
  change retainedRelativeSimplexCoordinate (pointComplementPair x) n σ hσ
      (((relativeChainProjection ℚ (pointComplementPair x)).f n).hom c) =
    retainedSimplexCoordinate (TopCat.toSSet.obj X) n σ c at hπ
  rw [hc x, map_zero] at hπ
  exact hπ.symm

end HodgeLean.Foundations.QuotientDuality
