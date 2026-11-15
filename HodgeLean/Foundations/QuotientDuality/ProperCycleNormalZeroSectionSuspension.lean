import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSuspensionNaturality

/-! # Specified tangential local classes on the actual normal zero section
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal base map from the zero-dimensional complex coordinate space to the normal origin.
Source: Munkres, Topology, section 18, constant continuous maps.
HC no distance; AV milestone no distance. -/
def properCycle_normal_zero_base_map (d : ℕ) :
    TopCat.of (Fin 0 → ℂ) ⟶ TopCat.of (Fin d → ℂ) :=
  TopCat.ofHom ⟨fun _ => 0, continuous_const⟩

/-- The actual zero base map preserves the specified relative complement condition because the original zero-dimensional point complement is empty.
Source: properCycle_normal_zero_base_map; uniqueness of functions on Fin 0.
HC no distance; AV milestone no distance. -/
theorem properCycle_normal_zero_base_complement (d : ℕ) :
    Set.MapsTo (properCycle_normal_zero_base_map d)
      ({0} : Set (Fin 0 → ℂ))ᶜ (Set.univ : Set (Fin d → ℂ))ᶜ := by
  intro z hz
  exact False.elim (hz (Subsingleton.elim z 0))

/-- The specified tangential standard local class carried by the literal normal zero section in each actual iterated real product.
Source: properCycle_iterated_real_local_class; properCycle_iterated_real_base_map; properCycle_normal_zero_base_complement.
HC no distance; AV milestone no distance. -/
def properCycle_normal_zero_section_local_class (d n : ℕ) :
    RelativeHomology ℚ
      (TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n)
        (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) Set.univ n)ᶜ) (0+n) :=
  relativeHomologyMap ℚ (0+n)
    (TopPair.ofSubsetHom (properCycle_iterated_real_base_map (properCycle_normal_zero_base_map d) n)
      (properCycle_iterated_real_point_complement_map (properCycle_normal_zero_base_map d)
        {0} Set.univ (properCycle_normal_zero_base_complement d) n))
    (properCycle_iterated_real_local_class 0 n)

/-- The actual composed support suspension of the specified tangential zero-section class has the exact original real-coordinate coefficient.
Source: properCycle_iterated_support_suspension_standard_map; properCycle_normal_zero_section_local_class.
HC no distance; AV milestone no distance. -/
theorem properCycle_normal_zero_section_local_class_suspension (d n : ℕ) :
    (properCycle_iterated_support_suspension_iso (TopCat.of (Fin d → ℂ)) Set.univ
      isClosed_univ 0 n).hom.hom (properCycle_normal_zero_section_local_class d n) =
      (-1 : ℚ)^n • relativeHomologyMap ℚ 0
        (TopPair.ofSubsetHom (properCycle_normal_zero_base_map d)
          (properCycle_normal_zero_base_complement d)) (standardComplexLocalClassMul 0) := by
  exact properCycle_iterated_support_suspension_standard_map (TopCat.of (Fin d → ℂ))
    0 (properCycle_normal_zero_base_map d) Set.univ
    (properCycle_normal_zero_base_complement d) isClosed_univ n

end HodgeLean.Foundations.QuotientDuality
