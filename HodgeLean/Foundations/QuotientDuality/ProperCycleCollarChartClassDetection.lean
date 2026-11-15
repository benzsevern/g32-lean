import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartCapPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarAmbientLocalDuality
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodPointMap

/-! # Original chart class detection by actual global support cap point values
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A zero point value of the actual global supported cap forces its represented original normal chart class to vanish, for an arbitrary contractible normal space.
Source: ProperCycleSupportCollar.chart_cap_point; ProperCycleSupportCollar.chart_ambient_local_support_cap_bijective; properCycle_neighborhood_point_map_bijective.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_class_zero_of_cap_point_zero
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] [ContractibleSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p : ℕ) (hp : Even p)
    (a : CohomologyWithSupport ℚ X S p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' {y}ᶜ)) p)
    (ha : relativeCohomologyMap ℚ p (b6m_subspacePairMap X (W : Set X) Sᶜ) a =
      relativeCohomologyMap ℚ p
        (TopPair.ofSubsetHom (X := TopCat.of W) (Y := TopCat.of (E × Y))
          (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter))
          (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1) b)
    (c : Homology ℚ X (p + Module.finrank ℝ E))
    (hc : Function.Bijective (orientationLine X (p + Module.finrank ℝ E) c z.val))
    (hzero : localOrientation (TopCat.of S) (Module.finrank ℝ E)
      (C.cap hS p (Module.finrank ℝ E) c a) z = 0) : b = 0 := by
  let F := C.chart_local_support_cap hS E Y e W hWe hWN hR y hflat z hzW hcenter
    p (Module.finrank ℝ E)
    ((properCycle_open_local_homology_iso X W ⟨z.val, hzW⟩
      (p + Module.finrank ℝ E)).inv.hom
      (localOrientation X (p + Module.finrank ℝ E) c z.val))
  have hF := C.chart_ambient_local_support_cap_bijective hS E Y e W hWe hWN hR y hflat
    z hzW hcenter p hp c hc
  let j : TopCat.of {s : S | s.val ∈ e.source} ⟶ TopCat.of S :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hj : IsOpenEmbedding j :=
    (e.open_source.preimage continuous_subtype_val).isOpenEmbedding_subtypeVal
  have hJ := properCycle_neighborhood_point_map_bijective j hj.isEmbedding ⟨z, hWe hzW⟩
    (hj.isOpen_range.mem_nhds ⟨⟨z, hWe hzW⟩, rfl⟩) (Module.finrank ℝ E)
  have h := C.chart_cap_point hS E Y e W hWe hWN hR y hflat z hzW hcenter
    p (Module.finrank ℝ E) a b ha c
  dsimp only at h
  apply hF.1
  apply hJ.1
  change relativeHomologyMap ℚ (Module.finrank ℝ E)
    (imagePointPairMap j Subtype.val_injective ⟨z, hWe hzW⟩) (F b) =
    relativeHomologyMap ℚ (Module.finrank ℝ E)
      (imagePointPairMap j Subtype.val_injective ⟨z, hWe hzW⟩) (F 0)
  rw [map_zero, map_zero]
  exact h.trans hzero

end HodgeLean.Foundations.QuotientDuality
