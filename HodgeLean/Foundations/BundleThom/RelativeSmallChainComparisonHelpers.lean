import HodgeLean.Foundations.BundleThom.SubcomplexPreimageRangeHelpers
import HodgeLean.Foundations.BundleThom.SingularSubsetPreimageHelpers

/-! # Actual relative small-chain comparison for a supplied binary open cover

The comparison targets the specified topological relative chain complex and retains the support-complement subspace.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

variable (X : TopCat) (Z : Set X)
private local instance : Mono (topologicalSubsetInclusion X Z) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective
private local instance : Mono (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) := by
  apply Functor.map_mono

/-- The actual small simplicial pair comparison into the supplied topological subspace pair.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain comparison. -/
def i1_relativeSmallSimplicialArrowComparison (K : (TopCat.toSSet.obj X).Subcomplex) :
    Arrow.mk (SSet.Subcomplex.homOfLE
      (inf_le_left : K ⊓ i1_singularSubsetRange X Z ≤ K)) ⟶
      Arrow.mk (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) := by
  let f := TopCat.toSSet.map (topologicalSubsetInclusion X Z)
  let e := i1_subcomplexPreimageRangeIso f K
  refine Arrow.homMk (e.inv ≫ (K.preimage f).ι) K.ι ?_
  change (e.inv ≫ (K.preimage f).ι) ≫ f =
    SSet.Subcomplex.homOfLE (inf_le_left : K ⊓ SSet.Subcomplex.range f ≤ K) ≫ K.ι
  rw [Category.assoc, ← i1_subcomplexPreimageRangeIso_hom_comp f K]
  change e.inv ≫ (e.hom ≫ _) = _
  exact e.inv_hom_id_assoc _

/-- The actual rational chain-arrow comparison induced by the specified small simplicial pair comparison.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain comparison. -/
def i1_relativeSmallChainArrowComparison (K : (TopCat.toSSet.obj X).Subcomplex) :
    (i1_relativeSubcomplexArrowFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj K ⟶
      (chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) Z) :=
  ((SSet.chainComplexFunctor.{0,0,1} (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).mapArrow.map
    (i1_relativeSmallSimplicialArrowComparison X Z K)

/-- The actual relative small-chain map into the supplied topological pair's rational relative chains.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain comparison. -/
def i1_relativeSmallChainComparison (K : (TopCat.toSSet.obj X).Subcomplex) :
    (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj K ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Z) :=
  (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map (i1_relativeSmallChainArrowComparison X Z K)

/-- Actual small-chain comparisons on the ambient and subspace components give the actual topological relative comparison.
Source: Hatcher, Algebraic Topology, §2.2, relative homology sequence and small-chain approximation. -/
theorem i1_relativeSmallChainComparison_quasiIso (K : (TopCat.toSSet.obj X).Subcomplex)
    (hsub : QuasiIso (SSet.chainComplexMap
      (K.preimage (TopCat.toSSet.map (topologicalSubsetInclusion X Z))).ι (ModuleCat.of ℚ ℚ)))
    (hamb : QuasiIso (SSet.chainComplexMap K.ι (ModuleCat.of ℚ ℚ))) :
    QuasiIso (i1_relativeSmallChainComparison X Z K) := by
  haveI : Mono ((i1_relativeSubcomplexArrowFunctor (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z)).obj K).hom := by
    dsimp [i1_relativeSubcomplexArrowFunctor, SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  haveI : Mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)).hom := by
    change Mono (SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) (ModuleCat.of ℚ ℚ))
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  apply i1_chainArrowCokernelMap_quasiIso (i1_relativeSmallChainArrowComparison X Z K)
  · haveI := hsub
    change QuasiIso (SSet.chainComplexMap
      ((i1_subcomplexPreimageRangeIso (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) K).inv ≫
        (K.preimage (TopCat.toSSet.map (topologicalSubsetInclusion X Z))).ι) (ModuleCat.of ℚ ℚ))
    dsimp only [SSet.chainComplexMap]
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  · exact hamb

/-- The actual relative small-chain inclusion of a supplied binary open cover is a quasi-isomorphism for every supplied subspace.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain approximation. -/
theorem i1_binaryRelativeSmallChainComparison_quasiIso (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (i1_relativeSmallChainComparison X Z
      (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V)) :=
  i1_relativeSmallChainComparison_quasiIso X Z _
    (i1_binarySmallChainInclusion_onSubset_quasiIso X U V Z hU hV hcover)
    (i1_binarySmallChainInclusion_quasiIso X U V hU hV hcover)

/-- The actual relative small chain-arrow comparison commutes with every supplied domain inclusion.
Source: Hatcher, Algebraic Topology, §2.2, naturality of small-chain comparison. -/
theorem i1_relativeSmallChainArrowComparison_naturality
    (K L : (TopCat.toSSet.obj X).Subcomplex) (hKL : K ≤ L) :
    (i1_relativeSubcomplexArrowFunctor (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z)).map (homOfLE hKL) ≫
        i1_relativeSmallChainArrowComparison X Z L = i1_relativeSmallChainArrowComparison X Z K := by
  haveI : Mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)).hom := by
    change Mono (SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) (ModuleCat.of ℚ ℚ))
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  have hr : ((i1_relativeSubcomplexArrowFunctor (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z)).map (homOfLE hKL) ≫
        i1_relativeSmallChainArrowComparison X Z L).right =
      (i1_relativeSmallChainArrowComparison X Z K).right := by
    change SSet.chainComplexMap (SSet.Subcomplex.homOfLE hKL) (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap L.ι (ModuleCat.of ℚ ℚ) = SSet.chainComplexMap K.ι (ModuleCat.of ℚ ℚ)
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  apply Arrow.hom_ext
  · apply (cancel_mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)).hom).mp
    rw [Arrow.w, Arrow.w, hr]
  · exact hr

/-- The actual relative small-chain comparison commutes with every supplied domain inclusion after taking cokernels.
Source: Hatcher, Algebraic Topology, §2.2, naturality of relative small chains. -/
theorem i1_relativeSmallChainComparison_naturality
    (K L : (TopCat.toSSet.obj X).Subcomplex) (hKL : K ≤ L) :
    (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z)).map (homOfLE hKL) ≫
        i1_relativeSmallChainComparison X Z L = i1_relativeSmallChainComparison X Z K := by
  change (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ ≫
    (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ =
      (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _
  rw [← CategoryTheory.Functor.map_comp, i1_relativeSmallChainArrowComparison_naturality]

end HodgeLean.Foundations.BundleThom
