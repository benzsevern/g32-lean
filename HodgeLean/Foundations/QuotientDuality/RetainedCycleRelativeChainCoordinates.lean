import HodgeLean.Foundations.QuotientDuality.RetainedCycleChainCoordinates

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A simplex coefficient absent from the subspace annihilates its actual chain map. -/
theorem retained_simplex_coordinate_subspace_zero (P : TopPair.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj P.fst) _⦋n⦌)
    (hσ : ∀ τ : (TopCat.toSSet.obj P.snd) _⦋n⦌, (TopCat.toSSet.map P.map).app (op ⦋n⦌) τ ≠ σ) :
    ((chainPairFunctor ℚ).obj P).hom.f n ≫
      ModuleCat.ofHom (retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ) = 0 := by
  apply SSet.chainComplex_hom_ext
  intro τ
  change (TopCat.toSSet.obj P.snd).ιChainComplex τ ≫
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of ℚ ℚ)).f n ≫
      ModuleCat.ofHom (retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ
    (Simplicial.chainOfSimplex ℚ ((TopCat.toSSet.map P.map).app (op ⦋n⦌) τ)) = 0
  rw [retained_simplex_coordinate_simplex]
  exact Finsupp.single_eq_of_ne (hσ τ).symm

/-- A simplex coefficient absent from the subspace descends to the actual relative-chain quotient. -/
def retainedRelativeSimplexCoordinate (P : TopPair.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj P.fst) _⦋n⦌)
    (hσ : ∀ τ : (TopCat.toSSet.obj P.snd) _⦋n⦌, (TopCat.toSSet.map P.map).app (op ⦋n⦌) τ ≠ σ) :
    RelativeCochain ℚ P n :=
  ((relativeChainProjectionComponentIsCokernelForCap ℚ P n).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ))
      (retained_simplex_coordinate_subspace_zero P n σ hσ))).hom

/-- The descended coordinate retains the literal coefficient after relative projection. -/
theorem retained_relative_simplex_coordinate_projection (P : TopPair.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj P.fst) _⦋n⦌)
    (hσ : ∀ τ : (TopCat.toSSet.obj P.snd) _⦋n⦌, (TopCat.toSSet.map P.map).app (op ⦋n⦌) τ ≠ σ) :
    (relativeChainProjection ℚ P).f n ≫ ModuleCat.ofHom (retainedRelativeSimplexCoordinate P n σ hσ) =
      ModuleCat.ofHom (retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ) :=
  (Cofork.IsColimit.π_desc (relativeChainProjectionComponentIsCokernelForCap ℚ P n)
    (t := CokernelCofork.ofπ
      (ModuleCat.ofHom (retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ))
      (retained_simplex_coordinate_subspace_zero P n σ hσ))).trans
        (CokernelCofork.π_ofπ _ _ _)

end HodgeLean.Foundations.QuotientDuality
