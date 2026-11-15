import HodgeLean.Foundations.BundleThom.SubsetRelativeSingularRangeHelpers

/-! # Actual relative chain coordinates for supplied topological domains

Both components are the actual singular range identifications before taking their relative cokernels.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

variable (X : TopCat) (Z U : Set X)
private local instance (T : TopCat) (S : Set T) : Mono (topologicalSubsetInclusion T S) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective
private local instance (T : TopCat) (S : Set T) :
    Mono (TopCat.toSSet.map (topologicalSubsetInclusion T S)) := by apply Functor.map_mono

/-- The actual singular pair of a supplied relative domain is isomorphic to its two ambient singular ranges.
Source: Hatcher, Algebraic Topology, §2.2, actual relative subspace identifications. -/
def i1_subsetRelativeSimplicialArrowIso :
    Arrow.mk (TopCat.toSSet.map (i1_subsetRelativePair X Z U).map) ≅
      Arrow.mk (SSet.Subcomplex.homOfLE (inf_le_left :
        i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X Z ≤ i1_singularSubsetRange X U)) :=
  Arrow.isoMk (i1_subsetRelativeSingularRangeIso X Z U)
    (asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (topologicalSubsetInclusion X U)))) (by
      ext n τ
      apply Subtype.ext
      rfl)

/-- The actual chain-arrow isomorphism from a relative domain to the fixed-subspace range diagram.
Source: Hatcher, Algebraic Topology, §2.2, relative chain identifications. -/
def i1_subsetRelativeChainArrowIso :
    (chainPairFunctor ℚ).obj (i1_subsetRelativePair X Z U) ≅
      (i1_relativeSubcomplexArrowFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
        (i1_singularSubsetRange X U) :=
  ((SSet.chainComplexFunctor.{0,0,1} (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).mapArrow.mapIso
    (i1_subsetRelativeSimplicialArrowIso X Z U)

/-- The actual relative chain isomorphism identifies the domain pair with its singular-range cokernel complex.
Source: Hatcher, Algebraic Topology, §2.2, rational relative chains. -/
def i1_subsetRelativeChainIso :
    (relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z U) ≅
      (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
        (i1_singularSubsetRange X U) :=
  (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).mapIso (i1_subsetRelativeChainArrowIso X Z U)

/-- The actual rational coclass coordinates for a supplied relative domain in the singular-range gluing diagram.
Source: Hatcher, Algebraic Topology, §3.1, relative coclass transport. -/
def i1_subsetRelativeCoclassEquiv (n : ℕ) :
    RelativeCohomology ℚ (i1_subsetRelativePair X Z U) n ≃ₗ[ℚ]
      ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
        (i1_singularSubsetRange X U)).linearDualCochainComplex.homology n :=
  i1_chainDualPullbackEquiv n (i1_subsetRelativeChainIso X Z U).inv

end HodgeLean.Foundations.BundleThom
