import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedRealLocalCoordinates

/-! # Specified real local classes in the actual iterated support pairs
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified standard real local class transported by the literal iterated complex normal coordinates.
Source: AlgebraicTopology.Singular.standardLocalClass; properCycle_iterated_real_local_pair_iso.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_real_local_class (d n : ℕ) :
    RelativeHomology ℚ
      (TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n)
        (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n)ᶜ) (d*2+n) :=
  relativeHomologyMap ℚ (d*2+n) (properCycle_iterated_real_local_pair_iso d n).hom
    (standardLocalClass ℚ (d*2+n))

/-- The actual support suspension of each specified iterated local class is minus the preceding specified local class.
Source: properCycle_real_support_suspension_standard_map; properCycle_iterated_real_local_pair_succ.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_local_class_suspension (d n : ℕ) :
    (properCycle_real_support_suspension_iso
      (properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n)
      (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n)
      (properCycle_real_point_support_isClosed (TopCat.of (Fin d → ℂ)) {0}
        isClosed_singleton n) (d*2+n)).hom.hom
      (properCycle_iterated_real_local_class d (n+1)) =
      -properCycle_iterated_real_local_class d n := by
  let X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n
  let T := properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n
  let f := TopCat.ofHom ⟨properCycle_iterated_real_local_coordinates d n,
    (properCycle_iterated_real_local_coordinates d n).continuous⟩
  let hT := properCycle_real_point_support_isClosed (TopCat.of (Fin d → ℂ)) {0}
    isClosed_singleton n
  have h := properCycle_real_support_suspension_standard_map X (d*2+n) f T
    (properCycle_iterated_real_local_complement_map d n) hT
  have hb : TopPair.ofSubsetHom f (properCycle_iterated_real_local_complement_map d n) =
      (properCycle_iterated_real_local_pair_iso d n).hom := by
    ext z : 2 <;> rfl
  have hz : relativeHomologyMap ℚ (d*2+n+1)
      (properCycle_real_support_zero_pair_map f {0} T
        (properCycle_iterated_real_local_complement_map d n))
      (relativeHomologyMap ℚ (d*2+n+1)
        (properCycle_real_point_support_pair_iso (TopCat.of (Fin (d*2+n) → ℝ))).inv
        (relativeHomologyMap ℚ (d*2+n+1)
          (properCycle_real_suspension_pair_iso (d*2+n)).hom
          (standardLocalClass ℚ (d*2+n+1)))) =
      properCycle_iterated_real_local_class d (n+1) := by
    unfold properCycle_iterated_real_local_class
    rw [← properCycle_iterated_real_local_pair_succ]
    simp only [relativeHomologyMap_comp, LinearMap.comp_apply]
    rfl
  dsimp only at h
  rw [hz, hb] at h
  exact h

/-- At the original normal base, the literal iterated local class is the specified complex local class in its uncast degree.
Source: AlgebraicTopology.Singular.standardComplexLocalClassMul; properCycle_complex_real_inverse_pair.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_local_class_zero (d : ℕ) :
    properCycle_iterated_real_local_class d 0 = standardComplexLocalClassMul d := by
  have hp : (properCycle_iterated_real_local_pair_iso d 0).hom =
      (standardComplexRealPairIso d).inv := by
    ext z : 2 <;> rfl
  unfold properCycle_iterated_real_local_class
  rw [hp]
  rfl

end HodgeLean.Foundations.QuotientDuality
