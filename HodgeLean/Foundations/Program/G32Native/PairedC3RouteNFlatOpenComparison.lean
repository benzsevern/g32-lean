import HodgeLean.Foundations.AlgebraicGeometry.ConormalFlatComparisonProofs
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartComparisonTransport

/-! # The natural comparison over an ambient open where the map is flat -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Flatness only on an ambient open suffices for invertibility of the
original ideal comparison after restriction to its inverse image.
Source: Hartshorne, Algebraic Geometry, II.5, flat pullback of ideals. -/
theorem paired_conormal_flat_open_ideal_map_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f)
    (U : W.Opens) [Flat (f ∣_ U)] :
    IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
      (idealPullbackMap i i' f g sq.w)) := by
  let V := f ⁻¹ᵁ U
  have hp : i' ⁻¹ᵁ V = g ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    change i' ⁻¹ᵁ (f ⁻¹ᵁ U) = g ⁻¹ᵁ (i ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← sq.w, Scheme.Hom.comp_preimage]
  let gU := g.resLE (i ⁻¹ᵁ U) (i' ⁻¹ᵁ V) hp.le
  have sqU : IsPullback gU (i' ∣_ V) (i ∣_ U) (f ∣_ U) := by
    have H := Scheme.Hom.isPullback_resLE sq (US := U) (UT := V) (UX := i ⁻¹ᵁ U)
      (UY := i' ⁻¹ᵁ V) le_rfl le_rfl (by rw [← hp, inf_idem])
    simpa only [V, Scheme.Hom.resLE_eq_morphismRestrict] using H
  haveI : IsIso (idealPullbackMap (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU sqU.w) :=
    idealPullbackMap_isIso_of_flat (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU sqU
  haveI := idealPullbackMap_open_isIso i U
  haveI := idealPullbackMap_open_isIso i' V
  exact paired_conormal_chart_ideal_map_isIso i i' (i ∣_ U) (i' ∣_ V)
    f g sq.w (f ∣_ U) gU sqU.w U.ι V.ι (i ⁻¹ᵁ U).ι (i' ⁻¹ᵁ V).ι
    (morphismRestrict_ι i U).symm (morphismRestrict_ι i' V).symm
    (morphismRestrict_ι f U)

#print axioms paired_conormal_flat_open_ideal_map_isIso
end HodgeLean.Foundations.Program.G32Native
