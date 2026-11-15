import HodgeLean.Foundations.QuotientDuality.RetainedCycleRelativeChainCoordinates

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A simplex coming from the subspace has zero relative projection. -/
theorem retained_relative_projection_subspace_simplex (P : TopPair.{0}) (n : ℕ)
    (τ : (TopCat.toSSet.obj P.snd) _⦋n⦌) :
    ((relativeChainProjection ℚ P).f n).hom
      (Simplicial.chainOfSimplex ℚ ((TopCat.toSSet.map P.map).app (op ⦋n⦌) τ)) = 0 := by
  have hz := congrArg (fun f => f.f n) (subspaceChainMap_relativeChainProjection ℚ P)
  have hn : (TopCat.toSSet.obj P.snd).ιChainComplex τ ≫
      (SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of ℚ ℚ)).f n =
      (TopCat.toSSet.obj P.fst).ιChainComplex
        ((TopCat.toSSet.map P.map).app (op ⦋n⦌) τ) := by
    rw [SSet.ι_chainComplexMap_f]
  have hv := ConcreteCategory.congr_hom (congrArg
    (fun f => (TopCat.toSSet.obj P.snd).ιChainComplex τ ≫ f) hz) (1 : ℚ)
  change ((relativeChainProjection ℚ P).f n).hom
    (((chainPairFunctor ℚ).obj P).hom.f n (Simplicial.chainOfSimplex ℚ τ)) = 0 at hv
  have he := ConcreteCategory.congr_hom hn (1 : ℚ)
  exact (congrArg (((relativeChainProjection ℚ P).f n).hom) he).symm.trans hv

/-- Coefficients outside the subspace detect zero after actual relative projection. -/
theorem retained_relative_projection_zero_of_coordinates (P : TopPair.{0}) (n : ℕ)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj P.fst) n)
    (hc : ∀ σ : (TopCat.toSSet.obj P.fst) _⦋n⦌,
      (∀ τ : (TopCat.toSSet.obj P.snd) _⦋n⦌,
        (TopCat.toSSet.map P.map).app (op ⦋n⦌) τ ≠ σ) →
      retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ c = 0) :
    ((relativeChainProjection ℚ P).f n).hom c = 0 := by
  classical
  have hr := LinearMap.congr_fun
    (retained_chain_from_coordinates_comp_coordinates (TopCat.toSSet.obj P.fst) n) c
  change retainedChainFromCoordinates (TopCat.toSSet.obj P.fst) n
    (retainedChainCoordinates (TopCat.toSSet.obj P.fst) n c) = c at hr
  rw [← hr, retainedChainFromCoordinates, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum]
  apply Finset.sum_eq_zero
  intro σ hσ
  have hn : retainedSimplexCoordinate (TopCat.toSSet.obj P.fst) n σ c ≠ 0 :=
    Finsupp.mem_support_iff.mp hσ
  have hi : ∃ τ : (TopCat.toSSet.obj P.snd) _⦋n⦌,
      (TopCat.toSSet.map P.map).app (op ⦋n⦌) τ = σ := by
    by_contra h
    exact hn (hc σ (by simpa only [not_exists] using h))
  obtain ⟨τ, rfl⟩ := hi
  rw [map_smul, retained_relative_projection_subspace_simplex, smul_zero]

end HodgeLean.Foundations.QuotientDuality
