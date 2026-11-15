import HodgeLean.Foundations.BundleThom.SubcomplexChainProjectionHelpers

/-! # Homology comparison for actual projected subcomplex unions

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology HomologicalComplex
namespace HodgeLean.Foundations.BundleThom

/-- Actual subcomplex projection from a union is equivalent on homology when both domains are equivalent and the intersection has the needed adjacent-degree maps.
Source: Hatcher, Algebraic Topology, §2.2, the Mayer–Vietoris comparison argument. -/
theorem i1_subcomplexProjection_sup_homology_isIso {X Y : SSet} (p : X ⟶ Y)
    (U V : X.Subcomplex)
    [QuasiIso (i1_subcomplexChainProjection p U)]
    [QuasiIso (i1_subcomplexChainProjection p V)] (n : ℕ)
    (ha : Epi (homologyMap (i1_subcomplexChainProjection p (U ⊓ V)) n))
    (hl : ∀ m, (ComplexShape.down ℕ).Rel n m →
      IsIso (homologyMap (i1_subcomplexChainProjection p (U ⊓ V)) m)) :
    IsIso (homologyMap (i1_subcomplexChainProjection p (U ⊔ V)) n) := by
  exact i1_chainSquareAugmentation_homology_isIso
    (i1_subcomplexChains_isPushout X U V).toCommSq
    (i1_subcomplexChainSequence_shortExact X U V)
    (i1_subcomplexChainProjection p (U ⊓ V))
    (i1_subcomplexChainProjection p U) (i1_subcomplexChainProjection p V)
    (i1_subcomplexChainProjection p (U ⊔ V))
    (i1_subcomplexChainProjection_naturality p _ _ inf_le_left)
    (i1_subcomplexChainProjection_naturality p _ _ inf_le_right)
    (i1_subcomplexChainProjection_naturality p _ _ le_sup_left)
    (i1_subcomplexChainProjection_naturality p _ _ le_sup_right) n ha hl

end HodgeLean.Foundations.BundleThom
