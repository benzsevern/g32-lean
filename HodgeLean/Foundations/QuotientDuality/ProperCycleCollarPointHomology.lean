import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointTriad
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadLocalHomology

/-! # Actual ambient point homology of the retained collar triad
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original local collar triad has exactly the original local ambient homology at the retained support point.
Source: ProperCycleSupportCollar.point_triad_union; properCycle_triad_local_homology_iso.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.pointTriadIso {X : TopCat.{0}} {S : Set X} [T1Space X]
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (z : S) (n : ℕ) :
    TriadRelativeHomology ℚ (TopCat.of C.neighborhood)
      (Subtype.val ⁻¹' Sᶜ) (C.retraction ⁻¹' ({z} : Set S)ᶜ) n ≅
      orientationGroup (TopCat.of C.neighborhood) n (C.inclusion z) :=
  properCycle_triad_local_homology_iso (TopCat.of C.neighborhood)
    (Subtype.val ⁻¹' Sᶜ) (C.retraction ⁻¹' ({z} : Set S)ᶜ)
    (hS.isOpen_compl.preimage continuous_subtype_val)
    (isClosed_singleton.isOpen_compl.preimage C.retraction.hom.continuous)
    (C.inclusion z) (C.point_triad_union z) n

end HodgeLean.Foundations.QuotientDuality
