import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalBaseClass
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportSuspensionDegreeTransport

/-! # Specified local classes for the actual iterated complex normal cap
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified standard local class in the actual normal-cap source, through the literal identity support-intersection map at every real coordinate.
Source: properCycle_iterated_real_local_class; properCycle_iterated_real_point_complement_map.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_source_class (d n : ℕ) :
    let X := TopCat.of (Fin d → ℂ)
    RelativeHomology ℚ (TopPair.ofSubset (X := properCycle_real_support_space X n)
      (properCycle_real_point_support X (({0} : Set X) ∩ Set.univ) n)ᶜ) (d*2+n) :=
  relativeHomologyMap ℚ (d*2+n)
    (TopPair.ofSubsetHom (properCycle_iterated_real_base_map (𝟙 (TopCat.of (Fin d → ℂ))) n)
      (properCycle_iterated_real_point_complement_map (𝟙 (TopCat.of (Fin d → ℂ)))
        {0} (({0} : Set (Fin d → ℂ)) ∩ Set.univ)
        (fun _ hz hP => hz hP.1) n)) (properCycle_iterated_real_local_class d n)

/-- The actual composed suspension of the specified normal-cap source class retains its exact original real-coordinate coefficient and original base class.
Source: properCycle_iterated_support_suspension_standard_map; properCycle_support_univ_pair_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_source_suspension (d n : ℕ) :
    let X := TopCat.of (Fin d → ℂ)
    (properCycle_iterated_support_suspension_iso X (({0} : Set X) ∩ Set.univ)
      (isClosed_singleton.inter isClosed_univ) (d*2) n).hom.hom
      (properCycle_complex_normal_source_class d n) =
      (-1 : ℚ)^n • relativeHomologyMap ℚ (d*2) (properCycle_support_univ_pair_iso X {0}).inv
        (standardComplexLocalClassMul d) := by
  let X := TopCat.of (Fin d → ℂ)
  let h : Set.MapsTo (𝟙 X) ({0} : Set X)ᶜ (({0} : Set X) ∩ Set.univ)ᶜ :=
    fun _ hz hP => hz hP.1
  have hp : TopPair.ofSubsetHom (𝟙 X) h = (properCycle_support_univ_pair_iso X {0}).inv := by
    ext z : 2 <;> rfl
  have hs := properCycle_iterated_support_suspension_standard_map X d (𝟙 X)
    (({0} : Set X) ∩ Set.univ) h (isClosed_singleton.inter isClosed_univ) n
  rw [hp] at hs
  exact hs

/-- The actual normal zero-section class retains its specified suspension coefficient through the literal source-degree transport.
Source: properCycle_iterated_zero_support_degree_transport; properCycle_normal_zero_section_local_class_suspension.
HC no distance; AV milestone no distance. -/
theorem properCycle_normal_zero_section_literal_suspension (d n : ℕ) :
    (properCycle_iterated_zero_support_suspension_iso (TopCat.of (Fin d → ℂ)) Set.univ
      isClosed_univ n).hom.hom
      (relativeHomologyDegreeCast (Nat.zero_add n) (properCycle_normal_zero_section_local_class d n)) =
      (-1 : ℚ)^n • relativeHomologyMap ℚ 0
        (TopPair.ofSubsetHom (properCycle_normal_zero_base_map d)
          (properCycle_normal_zero_base_complement d)) (standardComplexLocalClassMul 0) := by
  rw [properCycle_iterated_zero_support_degree_transport]
  exact properCycle_normal_zero_section_local_class_suspension d n

end HodgeLean.Foundations.QuotientDuality
