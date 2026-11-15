import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarAmbientFundamental
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointCap

/-! # Locality of the actual support cap in the specified ambient orientation
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual point value of the constructed support cap is the original local collar triad cap evaluated on the specified original ambient local orientation through actual point excision.
Source: ProperCycleSupportCollar.cap_point_triad; ProperCycleSupportCollar.pointAmbient_fundamental.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_point_local {X : TopCat.{0}} {S : Set X} [T1Space X]
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (z : S) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p+q)) :
    let U := TopCat.of C.neighborhood
    let A : Set U := Subtype.val ⁻¹' Sᶜ
    let B : Set U := C.retraction ⁻¹' ({z} : Set S)ᶜ
    localOrientation (TopCat.of S) q (C.cap hS p q c a) z =
      relativeHomologyMap ℚ q (C.pointPairMap z)
        (triadCapCohomologyLinear ℚ U A B p q
          (relativeCohomologyMap ℚ p (b6m_subspacePairMap X C.neighborhood Sᶜ) a)
          ((C.pointAmbientIso hS z (p+q)).inv.hom
            (localOrientation X (p+q) c (C.inclusion z).val))) := by
  dsimp only
  rw [C.cap_point_triad hS z p q a c]
  let e := (C.pointAmbientIso hS z (p+q)).toLinearEquiv
  have hh := C.pointAmbient_fundamental hS z (p+q) c
  change e _ = localOrientation X (p+q) c (C.inclusion z).val at hh
  have he := congrArg e.symm hh
  rw [e.symm_apply_apply] at he
  rw [he]
  rfl

end HodgeLean.Foundations.QuotientDuality
