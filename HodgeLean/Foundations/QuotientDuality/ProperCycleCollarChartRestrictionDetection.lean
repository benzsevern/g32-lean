import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartClassDetection
import HodgeLean.Foundations.QuotientDuality.ProperCycleFullChartSupportedModel
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalProjectionPullback

/-! # Actual supported restriction detection by global collar cap point values
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A zero actual global cap point value forces the original supported restriction on a full-target contractible-normal chart to vanish, using its constructed chart model.
Source: properCycle_full_chart_supported_model; ProperCycleSupportCollar.chart_class_zero_of_cap_point_zero; ProperCycleSupportCollar.chart_neighborhood.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_restriction_zero_of_cap_point_zero
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] [ContractibleSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (htarget : e.target = Set.univ)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hz : z.val ∈ e.source) (hcenter : e z.val = (0, y))
    (p : ℕ) (hp : Even p) (a : CohomologyWithSupport ℚ X S p)
    (c : Homology ℚ X (p + Module.finrank ℝ E))
    (hc : Function.Bijective (orientationLine X (p + Module.finrank ℝ E) c z.val))
    (hzero : localOrientation (TopCat.of S) (Module.finrank ℝ E)
      (C.cap hS p (Module.finrank ℝ E) c a) z = 0) :
    relativeCohomologyMap ℚ p (b6m_subspacePairMap X e.source Sᶜ) a = 0 := by
  obtain ⟨b, hb⟩ := properCycle_full_chart_supported_model X S E Y e htarget y hflat p a
  obtain ⟨W, hzW, hWe, hWN, hR⟩ := C.chart_neighborhood e z hz
  have ha := hb (W : Set X) hWe
  have ha' : relativeCohomologyMap ℚ p (b6m_subspacePairMap X (W : Set X) Sᶜ) a =
      relativeCohomologyMap ℚ p
        (TopPair.ofSubsetHom (X := TopCat.of W) (Y := TopCat.of (E × Y))
          (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter))
          (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1) b := by
    refine ha.trans (properCycle_product_support_pullback_eq_of_normal_eq E Y {y} _ _ _ ?_ p b)
    ext x : 2
    · apply Subtype.ext
      exact (congrArg Prod.snd
        (C.chart_retraction_point_pair_value E Y e W hWe hWN hR y hflat z hzW hcenter x.val)).symm
    · exact (congrArg Prod.snd
        (C.chart_retraction_point_pair_value E Y e W hWe hWN hR y hflat z hzW hcenter x)).symm
  have hbzero := C.chart_class_zero_of_cap_point_zero hS E Y e W hWe hWN hR y hflat
    z hzW hcenter p hp a b ha' c hc hzero
  have h := hb e.source Set.Subset.rfl
  rw [hbzero, map_zero] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
