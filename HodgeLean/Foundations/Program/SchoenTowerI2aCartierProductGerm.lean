import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealGerm
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealProduct
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk
import HodgeLean.Foundations.Program.SchoenCycleCartierAlgebra

/-! Nonzero generators of pulled-back Cartier products in actual stalks.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A finite product of locally free rank-one ideals pulled back by dominant maps has a nonzero generator in the actual source stalk. -/
theorem s2v_i2a_cartier_product_germ_generator
    (X : Scheme.{0}) [IsIntegral X] {J : Type} [Fintype J]
    (Y : J → Scheme.{0}) [∀ j, IsIntegral (Y j)]
    (f : ∀ j, X ⟶ Y j) [∀ j, IsDominant (f j)]
    (I : ∀ j, (Y j).IdealSheafData) (x : X)
    (hfree : ∀ j, ∃ V : (Y j).affineOpens, f j x ∈ V.1 ∧
      Nonempty (((I j).ideal V) ≃ₗ[Γ(Y j, V)] Γ(Y j, V)))
    (U : X.affineOpens) (hxU : x ∈ U.1) :
    ∃ e : X.presheaf.stalk x, e ≠ 0 ∧
      (((∏ j, (I j).comap (f j)).ideal U).map
        (X.presheaf.germ U.1 x hxU).hom) = Ideal.span {e} := by
  classical
  have hlocal (j : J) : ∃ e : X.presheaf.stalk x, e ≠ 0 ∧
      ((((I j).comap (f j)).ideal U).map
        (X.presheaf.germ U.1 x hxU).hom) = Ideal.span {e} := by
    obtain ⟨V, hxV, ⟨E⟩⟩ := hfree j
    letI : Nonempty V.1 := ⟨⟨f j x, hxV⟩⟩
    obtain ⟨z, hz, hreg⟩ := s2e_free_ideal_regular_generator ((I j).ideal V) E
    have hz_ne : z ≠ 0 := by
      intro h
      have H := hreg (a₁ := 1) (a₂ := 0) (by simp only [h, mul_zero])
      exact one_ne_zero H
    have hzg : (Y j).presheaf.germ V.1 (f j x) hxV z ≠ 0 := by
      intro h
      exact hz_ne (germ_injective_of_isIntegral (Y j) (f j x) hxV
        (h.trans (map_zero _).symm))
    have hφ : Function.Injective ((f j).stalkMap x).hom := by
      intro a b hab
      apply (IsFractionRing.injective ((Y j).presheaf.stalk (f j x)) (Y j).functionField)
      apply (s2v_l1b_functionFieldPullback (f j)).hom.injective
      rw [s2v_l1b_divisor_generic_stalk, s2v_l1b_divisor_generic_stalk, hab]
    refine ⟨(f j).stalkMap x ((Y j).presheaf.germ V.1 (f j x) hxV z), ?_, ?_⟩
    · intro h
      exact hzg (hφ (h.trans (map_zero _).symm))
    · rw [s2v_l1b_divisor_comap_ideal_germ (f j) (I j) x V U hxV hxU,
        hz, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  choose e he hI using hlocal
  refine ⟨∏ j, e j, Finset.prod_ne_zero_iff.mpr (fun j _ => he j), ?_⟩
  rw [s2v_l1b_divisor_ideal_germ_product]
  simp only [hI, Ideal.prod_span_singleton]

end HodgeLean.Foundations.Program
