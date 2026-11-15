import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalIteratedClasses

/-! # Literal relative pair map for the specified normal cap source class
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified normal-cap source class is carried by the actual local coordinate pair map followed by literal identity support transport.
Source: properCycle_iterated_real_local_pair_iso; properCycle_iterated_real_point_complement_map.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_source_pair_map (d n : ℕ) :
    puncturedPair ℝ (d*2+n) ⟶
      TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n)
        (properCycle_real_point_support (TopCat.of (Fin d → ℂ))
          (({0} : Set (Fin d → ℂ)) ∩ Set.univ) n)ᶜ :=
  (properCycle_iterated_real_local_pair_iso d n).hom ≫
    TopPair.ofSubsetHom (properCycle_iterated_real_base_map (𝟙 (TopCat.of (Fin d → ℂ))) n)
      (properCycle_iterated_real_point_complement_map (𝟙 (TopCat.of (Fin d → ℂ)))
        {0} (({0} : Set (Fin d → ℂ)) ∩ Set.univ) (fun _ hz hP => hz hP.1) n)

/-- The specified normal-cap source class is exactly the image of the original standard real class under its actual relative pair map.
Source: properCycle_complex_normal_source_class; properCycle_complex_normal_source_pair_map; relativeHomologyMap_comp.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_source_class_pair (d n : ℕ) :
    properCycle_complex_normal_source_class d n =
      relativeHomologyMap ℚ (d*2+n) (properCycle_complex_normal_source_pair_map d n)
        (standardLocalClass ℚ (d*2+n)) := by
  simp only [properCycle_complex_normal_source_pair_map, relativeHomologyMap_comp,
    LinearMap.comp_apply, properCycle_complex_normal_source_class, properCycle_iterated_real_local_class]

end HodgeLean.Foundations.QuotientDuality
