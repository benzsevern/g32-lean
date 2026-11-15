import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportSuspensionNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportStandardComparison

/-! # Specified local class coefficients under actual real coordinate transport
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual support suspension retains the specified negative standard local coefficient after literal real-product coordinate transport.
Source: properCycle_real_support_suspension_naturality; properCycle_real_support_suspension_standard.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_standard_map
    (X : TopCat.{0}) (d : ℕ) (f : TopCat.of (Fin d → ℝ) ⟶ X)
    (T : Set X) (h : Set.MapsTo f ({0} : Set (Fin d → ℝ))ᶜ Tᶜ) (hT : IsClosed T) :
    let z := relativeHomologyMap ℚ (d+1)
      (properCycle_real_point_support_pair_iso (TopCat.of (Fin d → ℝ))).inv
      (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
        (standardLocalClass ℚ (d+1)))
    (properCycle_real_support_suspension_iso X T hT d).hom.hom
      (relativeHomologyMap ℚ (d+1)
        (properCycle_real_support_zero_pair_map f {0} T h) z) =
      -relativeHomologyMap ℚ d (TopPair.ofSubsetHom f h) (standardLocalClass ℚ d) := by
  let z := relativeHomologyMap ℚ (d+1)
    (properCycle_real_point_support_pair_iso (TopCat.of (Fin d → ℝ))).inv
    (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
      (standardLocalClass ℚ (d+1)))
  have he := ConcreteCategory.congr_hom
    (properCycle_real_support_suspension_naturality f {0} T h isClosed_singleton hT d) z
  change (properCycle_real_support_suspension_iso X T hT d).hom.hom
      (relativeHomologyMap ℚ (d+1) (properCycle_real_support_zero_pair_map f {0} T h) z) =
    relativeHomologyMap ℚ d (TopPair.ofSubsetHom f h)
      ((properCycle_real_support_suspension_iso (TopCat.of (Fin d → ℝ)) {0}
        isClosed_singleton d).hom.hom z) at he
  rw [properCycle_real_support_suspension_standard d, map_neg] at he
  exact he

/-- The specified complex real-coordinate inverse preserves the actual point-complement condition.
Source: AlgebraicTopology.Singular.standardComplexRealPairIso; Complex.piCoordCLE.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_real_inverse_preserves_complement (d : ℕ) :
    Set.MapsTo (TopCat.ofHom ⟨(complexRealHomeomorph d).symm, (complexRealHomeomorph d).symm.continuous⟩)
      ({0} : Set (Fin (d*2) → ℝ))ᶜ ({0} : Set (Fin d → ℂ))ᶜ := by
  intro z hz
  change (Complex.piCoordCLE d).symm z ≠ 0
  exact fun he => hz ((Complex.piCoordCLE d).symm.map_eq_zero_iff.mp he)

/-- The original pair map for the inverse complex real coordinates is the specified inverse point-pair isomorphism.
Source: AlgebraicTopology.Singular.standardComplexRealPairIso.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_real_inverse_pair (d : ℕ) :
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨(complexRealHomeomorph d).symm,
        (complexRealHomeomorph d).symm.continuous⟩)
      (properCycle_complex_real_inverse_preserves_complement d) =
      (standardComplexRealPairIso d).inv := by
  ext z : 2 <;> rfl

/-- The actual real support suspension over the complex normal coordinates sends the specified transported real class to minus the specified complex local class.
Source: properCycle_real_support_suspension_standard_map; AlgebraicTopology.Singular.standardComplexLocalClassMul.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_complex_normal (d : ℕ) :
    let f := TopCat.ofHom ⟨(complexRealHomeomorph d).symm,
      (complexRealHomeomorph d).symm.continuous⟩
    let z := relativeHomologyMap ℚ (d*2+1)
      (properCycle_real_point_support_pair_iso (TopCat.of (Fin (d*2) → ℝ))).inv
      (relativeHomologyMap ℚ (d*2+1) (properCycle_real_suspension_pair_iso (d*2)).hom
        (standardLocalClass ℚ (d*2+1)))
    (properCycle_real_support_suspension_iso (TopCat.of (Fin d → ℂ)) {0}
      isClosed_singleton (d*2)).hom.hom
      (relativeHomologyMap ℚ (d*2+1)
        (properCycle_real_support_zero_pair_map f {0} {0}
          (properCycle_complex_real_inverse_preserves_complement d)) z) =
      -standardComplexLocalClassMul d := by
  have h := properCycle_real_support_suspension_standard_map
    (TopCat.of (Fin d → ℂ)) (d*2)
    (TopCat.ofHom ⟨(complexRealHomeomorph d).symm,
      (complexRealHomeomorph d).symm.continuous⟩) {0}
    (properCycle_complex_real_inverse_preserves_complement d) isClosed_singleton
  rw [properCycle_complex_real_inverse_pair d] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
