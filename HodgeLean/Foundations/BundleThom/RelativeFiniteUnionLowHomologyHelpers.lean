import HodgeLean.Foundations.BundleThom.BiproductHomologyVanishingHelpers
import HodgeLean.Foundations.BundleThom.ShortExactRightHomologyVanishingHelpers
import HodgeLean.Foundations.BundleThom.RelativeSubcomplexMonomorphismHelpers

/-! # Low-degree homology of actual relative chain unions

The intersection–union sequence retains the fixed relative subcomplex throughout.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- A union of two actual ambient subcomplexes with vanishing relative degree-zero homology has vanishing relative degree-zero homology.
Source: Hatcher, Algebraic Topology, §2.2, relative intersection–union sequence. -/
theorem i1_relativeSubcomplexSupHomologyZero_isZero (X : SSet) (Z U V : X.Subcomplex)
    (hu : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj U).homology 0))
    (hv : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj V).homology 0)) :
    IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U ⊔ V)).homology 0) := by
  exact i1_shortExactRightHomologyZero_isZero (i1_relativeSubcomplexChainSequence X Z U V)
    (i1_relativeSubcomplexChainSequence_shortExact X Z U V)
    (i1_biprodHomology_isZero _ _ 0 hu hv)

/-- Relative degree-one homology of a binary chain union vanishes when both domains vanish in degree one and their intersection vanishes in degree zero.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris. -/
theorem i1_relativeSubcomplexSupHomologyOne_isZero (X : SSet) (Z U V : X.Subcomplex)
    (hu : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj U).homology 1))
    (hv : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj V).homology 1))
    (hi : IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U ⊓ V)).homology 0)) :
    IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U ⊔ V)).homology 1) := by
  exact i1_shortExactRightHomologySuccessor_isZero (i1_relativeSubcomplexChainSequence X Z U V)
    (i1_relativeSubcomplexChainSequence_shortExact X Z U V) 0
    (i1_biprodHomology_isZero _ _ 1 hu hv) hi

end HodgeLean.Foundations.BundleThom
