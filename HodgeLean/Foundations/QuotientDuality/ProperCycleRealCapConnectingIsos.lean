import HodgeLean.Foundations.QuotientDuality.ProperCycleInverseConnectingCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapMiddleVanishing

/-! # Actual real half-ray connecting isomorphisms for the normal cap
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual half-ray contractions make the original fixed-relative source connecting map an isomorphism.
Source: Hatcher, Algebraic Topology, sections 2.1–2.2; properCycle_real_cap_middle_isZero.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_source_connecting_iso
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (p q : ℕ) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_fixed_subcomplex_sequence A P Q).X₃.homology (p+(q+1)) ≅
      (properCycle_fixed_subcomplex_sequence A P Q).X₁.homology (p+q) := by
  dsimp only
  exact (properCycle_fixed_subcomplex_sequence_shortExact (TopCat.of (ℝ × Y))
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ))
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ)
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ)).δIso
    (p+(q+1)) (p+q) (Nat.add_assoc p q 1).symm
    (properCycle_real_cap_middle_isZero Y S T hS hT (p+(q+1))).1
    (properCycle_real_cap_middle_isZero Y S T hS hT (p+q)).1

/-- Actual half-ray contractions make the original target connecting map an isomorphism.
Source: Hatcher, Algebraic Topology, sections 2.1–2.2; properCycle_real_cap_middle_isZero.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_target_connecting_iso
    (Y : TopCat.{0}) (T : Set Y) (hT : IsClosed T) (q : ℕ) :
    let X := TopCat.of (ℝ × Y)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_subcomplex_quotient_sequence P Q).X₃.homology (q+1) ≅
      (properCycle_subcomplex_quotient_sequence P Q).X₁.homology q := by
  dsimp only
  exact (properCycle_subcomplex_quotient_sequence_shortExact (TopCat.of (ℝ × Y))
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ)
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ)).δIso
    (q+1) q rfl
    (properCycle_real_cap_middle_isZero Y Set.univ T isClosed_univ hT (q+1)).2
    (properCycle_real_cap_middle_isZero Y Set.univ T isClosed_univ hT q).2

end HodgeLean.Foundations.QuotientDuality
