import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionSupportBaseUnit
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalZeroSectionUnit
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeUnitDetection
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-! # Actual normal cap base class with specified complex normalization
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original normalized complex normal cap at the actual base sends the specified normal class to the specified normal zero-section class.
Source: properCycle_union_support_normalized_base_unit; properCycle_normal_zero_base_unit; properCycle_relative_unit_injective.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_base_class (d : ℕ) :
    let X := TopCat.of (Fin d → ℂ)
    let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
      ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
    (properCycle_union_relative_support_cap X {0} Set.univ isClosed_singleton isClosed_univ
      (d*2) 0 (normalizedRelativeCoclass (standardComplexLocalClassMul d) hz)).hom
      (relativeHomologyMap ℚ (d*2) (properCycle_support_univ_pair_iso X {0}).inv
        (standardComplexLocalClassMul d)) =
      relativeHomologyMap ℚ 0 (TopPair.ofSubsetHom (properCycle_normal_zero_base_map d)
        (properCycle_normal_zero_base_complement d)) (standardComplexLocalClassMul 0) := by
  let X := TopCat.of (Fin d → ℂ)
  let P := TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ
  letI := HodgeLean.RealDefs.isIso_relativeChainProjection P
    ⟨fun z => z.2 (Set.mem_univ z.1)⟩
  let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
    ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
  letI : IsIso (P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ)) :=
    inferInstanceAs (IsIso ((TopCat.of (Fin d → ℂ)).singularHomology₀ε (ModuleCat.of ℚ ℚ)))
  apply (properCycle_relative_unit_injective P)
  exact (properCycle_union_support_normalized_base_unit X {0} isClosed_singleton
    (d*2) (by exact ⟨d, by omega⟩) (standardComplexLocalClassMul d) hz).trans
    (properCycle_normal_zero_base_unit d).symm

end HodgeLean.Foundations.QuotientDuality
