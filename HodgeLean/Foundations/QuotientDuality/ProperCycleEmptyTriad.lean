import HodgeLean.Foundations.QuotientDuality.ProperCycleProductCapSuspension
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalCapDuality

/-! # The actual empty second subspace of an original triad -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual singular chain complex of the empty subspace vanishes in every degree.
Source: Hatcher, Algebraic Topology, section 2.1, singular chains of the empty space.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_subspace_chains_isZero (X : TopCat.{0}) :
    IsZero (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset (X := X) (∅ : Set X)).snd) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro σ
  exact (((TopPair.ofSubset (X := X) (∅ : Set X)).snd.toSSetObjEquiv _ σ)
    StdSimplex.barycenter).2.elim

/-- The original triad chain complex with empty second subspace is the original relative chain complex of the first pair.
Source: Hatcher, Algebraic Topology, section 3.3, the relative cap base case.
HC no distance; AV milestone no distance. -/
def properCycle_empty_triad_relative_iso (X : TopCat.{0}) (A : Set X) :
    triadRelativeChainComplex ℚ X A ∅ ≅
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A) := by
  let CA := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset (X := X) A).snd
  let CB := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset (X := X) (∅ : Set X)).snd
  have hB : IsZero CB := properCycle_empty_subspace_chains_isZero X
  let e : CA ≅ CA ⊞ CB :=
    { hom := biprod.inl
      inv := biprod.fst
      hom_inv_id := biprod.inl_fst
      inv_hom_id := by
        have ht : (biprod.fst : CA ⊞ CB ⟶ CA) ≫ biprod.inl +
            (biprod.snd : CA ⊞ CB ⟶ CB) ≫ biprod.inr = 𝟙 _ := biprod.total
        rw [hB.eq_of_tgt (biprod.snd : CA ⊞ CB ⟶ CB) 0, zero_comp, add_zero] at ht
        exact ht }
  have he : e.hom ≫ triadSubspaceChainMap ℚ X A ∅ =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).hom := by
    dsimp only [e, triadSubspaceChainMap]
    exact biprod.inl_desc _ _
  letI : IsIso e.hom := e.isIso_hom
  exact (cokernelIsoOfEq he.symm ≪≫
    cokernelEpiComp e.hom (triadSubspaceChainMap ℚ X A ∅)).symm

/-- The empty-triad identification retains the original ambient relative chain projection.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap chain models.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_triad_relative_projection (X : TopCat.{0}) (A : Set X) :
    triadRelativeChainProjection ℚ X A ∅ ≫ (properCycle_empty_triad_relative_iso X A).hom =
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) A) := by
  simp [properCycle_empty_triad_relative_iso, triadRelativeChainProjection,
    relativeChainProjection, Category.assoc, cokernelEpiComp]

/-- The original absolute-to-relative projection for the empty actual subspace is an isomorphism of chain complexes.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains modulo the empty subspace.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_relative_projection_isIso (X : TopCat.{0}) :
    IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) := by
  have h0 : ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (∅ : Set X))).hom = 0 :=
    (properCycle_empty_subspace_chains_isZero X).eq_of_src _ _
  exact cokernel.π_of_zero h0

end HodgeLean.Foundations.QuotientDuality
