import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalRealCapSuspension

/-! # Suspending tangential support in the actual relative cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Adding one real tangential support coordinate preserves bijectivity of the original relative cohomology cap with its class pulled back by the actual projection.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, product contraction and cap suspension.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_support_cap_suspension_bijective
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p)
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y Sᶜ Tᶜ p q a)) :
    let X := TopCat.of (ℝ × Y)
    let f : X ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    Function.Bijective (triadCapCohomologyLinear ℚ X (Prod.snd ⁻¹' Sᶜ)
      {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q + 1)
      (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f
        (show Set.MapsTo f (Prod.snd ⁻¹' Sᶜ) Sᶜ from fun _ h => h)) a)) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A : Set X := Prod.snd ⁻¹' Sᶜ
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  have hI : P ∩ Q = Prod.snd ⁻¹' Tᶜ := by
    ext z
    change (¬ (0 ≤ z.1 ∧ z.2 ∈ T) ∧ ¬ (z.1 ≤ 0 ∧ z.2 ∈ T)) ↔ z.2 ∉ T
    constructor
    · intro h ht
      rcases le_total 0 z.1 with hz | hz
      · exact h.1 ⟨hz, ht⟩
      · exact h.2 ⟨hz, ht⟩
    · tauto
  have hU : P ∪ Q = {z : ℝ × Y | z.1 = 0 ∧ z.2 ∈ T}ᶜ := by
    ext z
    change (¬ (0 ≤ z.1 ∧ z.2 ∈ T) ∨ ¬ (z.1 ≤ 0 ∧ z.2 ∈ T)) ↔ ¬ (z.1 = 0 ∧ z.2 ∈ T)
    constructor
    · rintro (h | h) ⟨hz, ht⟩ <;> exact h ⟨by simp [hz], ht⟩
    · intro h
      by_cases ht : z.2 ∈ T
      · by_cases hz : 0 ≤ z.1
        · right
          rintro ⟨hz', _⟩
          exact h ⟨le_antisymm hz' hz, ht⟩
        · exact Or.inl (fun h => hz h.1)
      · exact Or.inl (fun h => ht h.2)
  have hlo := properCycle_product_triad_cap_bijective ℝ Y Sᶜ Tᶜ
    hS.isOpen_compl hT.isOpen_compl p q a hc
  have h := properCycle_original_real_cohomology_cap_suspension_bijective Y S T hS hT p q hp
  dsimp only at h
  change ∀ b, Function.Bijective (triadCapCohomologyLinear ℚ X A (P ∩ Q) p q b) →
    Function.Bijective (triadCapCohomologyLinear ℚ X A (P ∪ Q) p (q + 1) b) at h
  rw [hI, hU] at h
  exact h _ hlo

end HodgeLean.Foundations.QuotientDuality
