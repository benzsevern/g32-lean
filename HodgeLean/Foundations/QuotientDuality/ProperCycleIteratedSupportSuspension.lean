import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedRealLocalClass

/-! # Actual iterated signed support suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Compose the actual signed support suspensions on the recursive real-product spaces.
Source: properCycle_real_support_suspension_iso; properCycle_real_point_support_isClosed.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_support_suspension_iso
    (Y : TopCat.{0}) (T : Set Y) (hT : IsClosed T) (q : ℕ) :
    (n : ℕ) → RelativeHomology ℚ
      (TopPair.ofSubset (X := properCycle_real_support_space Y n)
        (properCycle_real_point_support Y T n)ᶜ) (q+n) ≅
      RelativeHomology ℚ (TopPair.ofSubset (X := Y) Tᶜ) q
  | 0 => Iso.refl _
  | n+1 => properCycle_real_support_suspension_iso (properCycle_real_support_space Y n)
      (properCycle_real_point_support Y T n) (properCycle_real_point_support_isClosed Y T hT n)
      (q+n) ≪≫ properCycle_iterated_support_suspension_iso Y T hT q n

/-- The composed actual support suspensions retain the exact original real-coordinate sign on the specified complex normal local class.
Source: properCycle_iterated_real_local_class_suspension; properCycle_iterated_real_local_class_zero.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_support_suspension_local_class (d n : ℕ) :
    (properCycle_iterated_support_suspension_iso (TopCat.of (Fin d → ℂ)) {0}
      isClosed_singleton (d*2) n).hom.hom (properCycle_iterated_real_local_class d n) =
      (-1 : ℚ)^n • standardComplexLocalClassMul d := by
  induction n with
  | zero =>
    change properCycle_iterated_real_local_class d 0 = (-1 : ℚ)^0 • standardComplexLocalClassMul d
    simpa only [pow_zero, one_smul] using properCycle_iterated_real_local_class_zero d
  | succ n ih =>
    change (properCycle_iterated_support_suspension_iso (TopCat.of (Fin d → ℂ)) {0}
      isClosed_singleton (d*2) n).hom.hom
      ((properCycle_real_support_suspension_iso
        (properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n)
        (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n)
        (properCycle_real_point_support_isClosed (TopCat.of (Fin d → ℂ)) {0}
          isClosed_singleton n) (d*2+n)).hom.hom
        (properCycle_iterated_real_local_class d (n+1))) = _
    rw [properCycle_iterated_real_local_class_suspension, map_neg, ih]
    simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- The actual signed support suspensions to degree zero, retaining the literal source degree at each stage.
Source: properCycle_real_support_suspension_iso; properCycle_real_point_support_isClosed.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_zero_support_suspension_iso
    (Y : TopCat.{0}) (T : Set Y) (hT : IsClosed T) :
    (n : ℕ) → RelativeHomology ℚ
      (TopPair.ofSubset (X := properCycle_real_support_space Y n)
        (properCycle_real_point_support Y T n)ᶜ) n ≅
      RelativeHomology ℚ (TopPair.ofSubset (X := Y) Tᶜ) 0
  | 0 => Iso.refl _
  | n+1 => properCycle_real_support_suspension_iso (properCycle_real_support_space Y n)
      (properCycle_real_point_support Y T n) (properCycle_real_point_support_isClosed Y T hT n) n ≪≫
      properCycle_iterated_zero_support_suspension_iso Y T hT n

end HodgeLean.Foundations.QuotientDuality
