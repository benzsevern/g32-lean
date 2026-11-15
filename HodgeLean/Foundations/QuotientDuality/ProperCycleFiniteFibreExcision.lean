import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteFibrePushforward
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedSupportMap

/-! # Actual finite fibre contributions computed on isolated neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual finite-fibre point contribution on a neighborhood class is the literal composite pair map from that isolated neighborhood.
Source: Hatcher, Algebraic Topology, section 2.2, excision and local degree.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_fibre_point_pushforward_on_neighborhood
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) [DecidableEq (f ⁻¹' {y})]
    (x : f ⁻¹' {y}) (U : Set X)
    (hisolate : ∀ z ∈ U, f z = y → z = x.val) (n : ℕ)
    (c : RelativeHomology ℚ (neighborhoodSupportComplementPair U ({x.val} : Set X)) n) :
    properCycle_finite_fibre_point_pushforward f y hfinite n x
      (relativeHomologyMap ℚ n (b6m_subspacePairMap X U ({x.val} : Set X)ᶜ) c) =
      relativeHomologyMap ℚ n
        (properCycle_isolated_support_pair_map X (f ⁻¹' {y}) U x.val hisolate ≫
          properCycle_fibre_complement_pair_map f y) c := by
  let E := properCycle_finite_support_localization X (f ⁻¹' {y}) hfinite n
  have hl := properCycle_isolated_support_map_localization X (f ⁻¹' {y}) U hfinite
    x.val x.property hisolate n c
  have hi := congrArg E.symm hl
  rw [LinearEquiv.symm_apply_apply] at hi
  change relativeHomologyMap ℚ n (properCycle_fibre_complement_pair_map f y)
    (E.symm (Pi.single x (relativeHomologyMap ℚ n
      (b6m_subspacePairMap X U ({x.val} : Set X)ᶜ) c))) = _
  rw [← hi, relativeHomologyMap_comp, LinearMap.comp_apply]

/-- The actual point contribution is computed by the original singleton excision inverse on every open isolated fibre neighborhood.
Source: Hatcher, Algebraic Topology, section 2.2, excision and local degree.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_fibre_point_pushforward_excision
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) [DecidableEq (f ⁻¹' {y})]
    (x : f ⁻¹' {y}) (U : Set X) (hU : IsOpen U) (hxU : x.val ∈ U)
    (hisolate : ∀ z ∈ U, f z = y → z = x.val) (n : ℕ)
    (c : orientationGroup X n x.val) :
    properCycle_finite_fibre_point_pushforward f y hfinite n x c =
      relativeHomologyMap ℚ n
        (properCycle_isolated_support_pair_map X (f ⁻¹' {y}) U x.val hisolate ≫
          properCycle_fibre_complement_pair_map f y)
        ((LinearEquiv.ofBijective
          (relativeHomologyMap ℚ n (b6m_subspacePairMap X U ({x.val} : Set X)ᶜ))
          (b6m_closed_support_excision_bijective ℚ hU isClosed_singleton
            (Set.singleton_subset_iff.mpr hxU) n)).symm c) := by
  let E := LinearEquiv.ofBijective
    (relativeHomologyMap ℚ n (b6m_subspacePairMap X U ({x.val} : Set X)ᶜ))
    (b6m_closed_support_excision_bijective ℚ hU isClosed_singleton
      (Set.singleton_subset_iff.mpr hxU) n)
  have h := properCycle_finite_fibre_point_pushforward_on_neighborhood
    f y hfinite x U hisolate n (E.symm c)
  change properCycle_finite_fibre_point_pushforward f y hfinite n x (E (E.symm c)) = _ at h
  rw [E.apply_symm_apply] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
