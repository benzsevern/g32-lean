import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapConnectingIsos

/-! # The actual inverse suspension square for the original normal cap
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual half-ray contractions supply both inverse connecting maps in the original cap square.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_subcomplex_mv_cap_inverse_connecting.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_inverse_square
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_real_cap_source_connecting_iso Y S T hS hT p q).inv ≫
        properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ =
      properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ ≫
        (properCycle_real_cap_target_connecting_iso Y T hT q).inv := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let eS := properCycle_real_cap_source_connecting_iso Y S T hS hT p q
  let eT := properCycle_real_cap_target_connecting_iso Y T hT q
  letI : IsIso ((properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δ
      (p+(q+1)) (p+q) (Nat.add_assoc p q 1).symm) := by
    change IsIso eS.hom
    infer_instance
  letI : IsIso ((properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (q+1) q rfl) := by
    change IsIso eT.hom
    infer_instance
  have h := properCycle_subcomplex_mv_cap_inverse_connecting X A P Q p q hp φ hA hφ
  change eS.inv ≫ properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ =
    properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ ≫ eT.inv at h
  exact h

/-- The original normal cap retains a specified class normalization through both actual negative real suspension lifts.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_real_cap_inverse_square.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_negative_suspension_normalization
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    ∀ (u : (properCycle_subcomplex_quotient (A ⊔ (P ⊓ Q))).homology (p+q))
      (v : (properCycle_subcomplex_quotient (P ⊓ Q)).homology q),
      (properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ).hom u = v →
      (properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ).hom
          ((properCycle_real_cap_source_connecting_iso Y S T hS hT p q).inv.hom (-u)) =
        (properCycle_real_cap_target_connecting_iso Y T hT q).inv.hom (-v) := by
  dsimp only
  intro u v huv
  have h := ConcreteCategory.congr_hom
    (properCycle_real_cap_inverse_square Y S T hS hT p q hp φ hA hφ) (-u)
  change _ = (properCycle_real_cap_target_connecting_iso Y T hT q).inv.hom
    ((properCycle_subcomplex_cap_homology_map _ _ p q hp φ hA hφ).hom (-u)) at h
  have hh : (properCycle_subcomplex_cap_homology_map _ _ p q hp φ hA hφ).hom (-u) = -v := by
    rw [map_neg, huv]
  exact h.trans (congrArg (properCycle_real_cap_target_connecting_iso Y T hT q).inv.hom hh)

end HodgeLean.Foundations.QuotientDuality
