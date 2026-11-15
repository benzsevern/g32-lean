import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeUnitAugmentation
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalZeroSectionSuspension

/-! # Original unit evaluation on the actual normal zero section
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual normal zero-section base class has original cup-unit evaluation one through the specified inverse empty-relative projection.
Source: properCycle_relative_unit_pushforward; properCycle_standard_complex_zero_unit; properCycle_normal_zero_base_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_normal_zero_base_unit (d : ℕ) :
    let P := TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) (Set.univ : Set (Fin d → ℂ))ᶜ
    letI := HodgeLean.RealDefs.isIso_relativeChainProjection P
      ⟨fun z => z.2 (Set.mem_univ z.1)⟩
    let E := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0
    cohomologyEquivDualHomology ℚ (TopCat.of (Fin d → ℂ)) 0
      (unit (R := ℚ) (TopCat.of (Fin d → ℂ)))
      (E.inv.hom (relativeHomologyMap ℚ 0
        (TopPair.ofSubsetHom (properCycle_normal_zero_base_map d)
          (properCycle_normal_zero_base_complement d)) (standardComplexLocalClassMul 0))) = 1 := by
  let P := TopPair.ofSubset (X := TopCat.of (Fin d → ℂ)) (Set.univ : Set (Fin d → ℂ))ᶜ
  letI := HodgeLean.RealDefs.isIso_relativeChainProjection P
    ⟨fun z => z.2 (Set.mem_univ z.1)⟩
  have h := properCycle_relative_unit_pushforward
    (TopPair.ofSubsetHom (properCycle_normal_zero_base_map d)
      (properCycle_normal_zero_base_complement d)) (standardComplexLocalClassMul 0)
  exact h.trans properCycle_standard_complex_zero_unit

end HodgeLean.Foundations.QuotientDuality
