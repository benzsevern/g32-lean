import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalIteratedClasses
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedCapBaseComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedUnionCapRecurrence

/-! # Actual iterated normal cap on the specified standard local classes
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original normal cap after any number of actual real tangential factors sends the specified standard source class to the specified tangential zero-section class, retaining its original source degree transport.
Source: properCycle_iterated_union_cap_suspension; properCycle_complex_normal_base_class; properCycle_complex_normal_source_suspension; properCycle_normal_zero_section_literal_suspension.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_complex_normal_cap_standard (d n : ℕ) :
    let X := TopCat.of (Fin d → ℂ)
    let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
      ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
    (properCycle_iterated_union_relative_cap X {0} Set.univ isClosed_singleton isClosed_univ
      (d*2) (normalizedRelativeCoclass (standardComplexLocalClassMul d) hz) n).hom
      (properCycle_complex_normal_source_class d n) =
      relativeHomologyDegreeCast (Nat.zero_add n) (properCycle_normal_zero_section_local_class d n) := by
  let X := TopCat.of (Fin d → ℂ)
  let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
    ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
  let a := normalizedRelativeCoclass (standardComplexLocalClassMul d) hz
  let Kn := properCycle_iterated_union_relative_cap X {0} Set.univ isClosed_singleton isClosed_univ
    (d*2) a n
  let K₀ := properCycle_iterated_union_relative_cap X {0} Set.univ isClosed_singleton isClosed_univ
    (d*2) a 0
  let tT := properCycle_iterated_zero_support_suspension_iso X Set.univ isClosed_univ n
  let tP := properCycle_iterated_support_suspension_iso X (({0} : Set X) ∩ Set.univ)
    (isClosed_singleton.inter isClosed_univ) (d*2) n
  let b := relativeHomologyMap ℚ (d*2) (properCycle_support_univ_pair_iso X {0}).inv
    (standardComplexLocalClassMul d)
  let t := relativeHomologyMap ℚ 0 (TopPair.ofSubsetHom (properCycle_normal_zero_base_map d)
    (properCycle_normal_zero_base_complement d)) (standardComplexLocalClassMul 0)
  have hb : K₀.hom b = t := by
    dsimp only [K₀]
    rw [properCycle_iterated_union_relative_cap_zero]
    exact properCycle_complex_normal_base_class d
  have hs := properCycle_complex_normal_source_suspension d n
  change tP.hom.hom (properCycle_complex_normal_source_class d n) = (-1 : ℚ)^n • b at hs
  have hc := ConcreteCategory.congr_hom
    (properCycle_iterated_union_cap_suspension X {0} Set.univ isClosed_singleton isClosed_univ
      (d*2) (by exact ⟨d, by omega⟩) a n) (properCycle_complex_normal_source_class d n)
  change tT.hom.hom (Kn.hom (properCycle_complex_normal_source_class d n)) =
    K₀.hom (tP.hom.hom (properCycle_complex_normal_source_class d n)) at hc
  rw [hs, map_smul, hb] at hc
  have ht := properCycle_normal_zero_section_literal_suspension d n
  change tT.hom.hom
    (relativeHomologyDegreeCast (Nat.zero_add n) (properCycle_normal_zero_section_local_class d n)) =
    (-1 : ℚ)^n • t at ht
  apply (ConcreteCategory.bijective_of_isIso tT.hom).1
  exact hc.trans ht.symm

end HodgeLean.Foundations.QuotientDuality
