import HodgeLean.Foundations.BundleThom.BinaryChainCoclassGluingHelpers

/-! # Gluing individual coclasses on actual relative subcomplex domains

The two input classes and their actual intersection restriction maps are retained.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Two actual relative subcomplex coclasses with equal intersection restriction have a union extension with both prescribed restrictions.
Source: Hatcher, Algebraic Topology, §3.1, relative Mayer–Vietoris gluing. -/
theorem i1_binaryRelativeSubcomplexCoclass_gluing (X : SSet) (Z U V : X.Subcomplex) (n : ℕ)
    (u : ((i1_relativeSubcomplexChainFunctor X Z).obj U).linearDualCochainComplex.homology n)
    (v : ((i1_relativeSubcomplexChainFunctor X Z).obj V).linearDualCochainComplex.homology n)
    (huv : i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor X Z).map
        (homOfLE (inf_le_left : U ⊓ V ≤ U))) u =
      i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor X Z).map
        (homOfLE (inf_le_right : U ⊓ V ≤ V))) v) :
    ∃ z : ((i1_relativeSubcomplexChainFunctor X Z).obj (U ⊔ V)).linearDualCochainComplex.homology n,
      i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor X Z).map
        (homOfLE (le_sup_left : U ≤ U ⊔ V))) z = u ∧
      i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor X Z).map
        (homOfLE (le_sup_right : V ≤ U ⊔ V))) z = v := by
  haveI := i1_relativeSubcomplexChainMap_mono X Z (U ⊓ V) U inf_le_left
  exact i1_binaryChainCoclass_gluing (i1_relativeSubcomplexChains_isPushout X Z U V) n u v huv

end HodgeLean.Foundations.BundleThom
