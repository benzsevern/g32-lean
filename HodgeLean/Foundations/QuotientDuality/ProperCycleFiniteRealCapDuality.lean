import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphCapTransport

/-! # Original cap duality in actual finite real tangential products -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original cap duality suspends into the actual finite real tangential product, retaining the original cohomology class along the literal normal projection.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative subdivision, cap suspension and naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_real_product_cap_bijective
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p)
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y Sᶜ Tᶜ p q a)) (n : ℕ) :
    Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of ((Fin n → ℝ) × Y))
      (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q + n)
      (relativeCohomologyMap ℚ p (properCycle_product_support_projection (Fin n → ℝ) Y S) a)) := by
  let Z := properCycle_real_support_space Y n
  let W := TopCat.of ((Fin n → ℝ) × Y)
  let e := properCycle_real_support_coordinates Y n
  let A : Set W := Prod.snd ⁻¹' Sᶜ
  let B : Set W := {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ
  let C : Set Z := (properCycle_real_normal_support Y S n)ᶜ
  let D : Set Z := (properCycle_real_point_support Y T n)ᶜ
  have hAC : ∀ z, e.symm z ∈ C ↔ z ∈ A := by
    intro z
    have h : e (e.symm z) ∈ Prod.snd ⁻¹' S ↔
        e.symm z ∈ properCycle_real_normal_support Y S n :=
      Set.ext_iff.mp (properCycle_real_support_coordinates_normal Y S n) _
    exact not_congr (by simpa only [e.apply_symm_apply, Set.mem_preimage] using h.symm)
  have hBD : ∀ z, e.symm z ∈ D ↔ z ∈ B := by
    intro z
    have h : e (e.symm z) ∈ {z : (Fin n → ℝ) × Y | z.1 = 0 ∧ z.2 ∈ T} ↔
        e.symm z ∈ properCycle_real_point_support Y T n :=
      Set.ext_iff.mp (properCycle_real_support_coordinates_point Y T n) _
    exact not_congr (by simpa only [e.apply_symm_apply, Set.mem_preimage] using h.symm)
  have hAo : IsOpen A := hS.isOpen_compl.preimage continuous_snd
  have hBo : IsOpen B := ((isClosed_eq continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hCo : IsOpen C := (properCycle_real_normal_support_isClosed Y S hS n).isOpen_compl
  have hDo : IsOpen D := (properCycle_real_point_support_isClosed Y T hT n).isOpen_compl
  have h := properCycle_homeomorph_triad_cap_bijective (X := W) (Y := Z) e.symm
    A B C D hAC hBD hAo hBo hCo hDo p (q + n)
    (properCycle_real_support_coclass Y S p a n)
    (properCycle_iterated_product_support_cap_bijective Y S T hS hT p q hp a hc n)
  have he : (TopPair.isoOfSubset e.symm hAC).hom =
      (properCycle_real_support_normal_pair_iso Y S n).inv := by
    ext z : 2 <;> rfl
  rw [he, properCycle_real_support_coclass_coordinates] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
