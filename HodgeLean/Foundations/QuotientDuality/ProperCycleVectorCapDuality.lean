import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteRealCapDuality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealVectorShift

/-! # Original cap duality with an actual finite dimensional tangential vector space -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original cap bijectivity extends to any actual finite dimensional real tangential factor with the original normal cohomology class pulled back by the product projection.
Source: Hatcher, Algebraic Topology, section 3.3, cap naturality in local vector coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_vector_product_cap_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p)
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y Sᶜ Tᶜ p q a)) :
    Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q + Module.finrank ℝ E)
      (relativeCohomologyMap ℚ p (properCycle_product_support_projection E Y S) a)) := by
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq
    (by simp only [Module.finrank_pi, Fintype.card_fin]; rfl)
  let X := TopCat.of (E × Y)
  let W := TopCat.of ((Fin n → ℝ) × Y)
  let e : X ≃ₜ W := L.toHomeomorph.prodCongr (Homeomorph.refl Y)
  let A : Set X := Prod.snd ⁻¹' Sᶜ
  let B : Set X := {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ
  let C : Set W := Prod.snd ⁻¹' Sᶜ
  let D : Set W := {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ
  have hAC : ∀ z, e z ∈ C ↔ z ∈ A := fun _ => Iff.rfl
  have hBD : ∀ z, e z ∈ D ↔ z ∈ B := by
    intro z
    apply not_congr
    change (L z.1 = 0 ∧ z.2 ∈ T) ↔ (z.1 = 0 ∧ z.2 ∈ T)
    constructor
    · rintro ⟨hz, ht⟩
      exact ⟨L.injective (hz.trans (map_zero L).symm), ht⟩
    · rintro ⟨hz, ht⟩
      exact ⟨by rw [hz, map_zero], ht⟩
  have hAo : IsOpen A := hS.isOpen_compl.preimage continuous_snd
  have hCo : IsOpen C := hS.isOpen_compl.preimage continuous_snd
  have hBo : IsOpen B := ((isClosed_eq continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hDo : IsOpen D := ((isClosed_eq continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have h := properCycle_homeomorph_triad_cap_bijective e A B C D hAC hBD hAo hBo hCo hDo p (q + n)
    (relativeCohomologyMap ℚ p (properCycle_product_support_projection (Fin n → ℝ) Y S) a)
    (properCycle_finite_real_product_cap_bijective Y S T hS hT p q hp a hc n)
  have he : (TopPair.isoOfSubset e hAC).hom ≫ properCycle_product_support_projection (Fin n → ℝ) Y S =
      properCycle_product_support_projection E Y S := by ext z : 2 <;> rfl
  have ha : relativeCohomologyMap ℚ p (TopPair.isoOfSubset e hAC).hom
      (relativeCohomologyMap ℚ p (properCycle_product_support_projection (Fin n → ℝ) Y S) a) =
      relativeCohomologyMap ℚ p (properCycle_product_support_projection E Y S) a := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, he]
  rw [ha] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
