import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorBinomialDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportBinomialResidues
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalMaps

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual categorical quotient descends the ratio of two nonzero functions with the same character. -/
theorem s2v_l1b_divisor_quotient_character_ratio
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (β : X ⟶ Y) [IsFinite β.left] [IsDominant β.left]
    (d : X ⟶ X) [IsIso d] (hd : d ≫ β = β)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      d ≫ f = f → ∃! u : Y ⟶ T, β ≫ u = f)
    (τ : X.left.functionField ≃+* X.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      X.left.fromSpecStalk (genericPoint X.left) =
      X.left.fromSpecStalk (genericPoint X.left) ≫ d.left)
    (t w ξ : X.left.functionField) (ht : t ≠ 0) (hw : w ≠ 0) (hξ : ξ ≠ 0)
    (htξ : τ t = ξ * t) (hwξ : τ w = ξ * w) :
    ∃ c : Y.left.functionField, c ≠ 0 ∧
      t = s2v_l1b_functionFieldPullback β.left c * w := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint Y.left) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint Y.left, hxU⟩⟩
  have hfixed : τ (t / w) = 1 * (t / w) := by
    rw [map_div₀, htξ, hwξ, mul_div_mul_left _ _ hξ, one_mul]
  obtain ⟨c, hc⟩ := s2v_l1b_divisor_generator_binomial X Y β d hd hcat ⟨U, hU⟩
    τ hτ (t / w) 1 1 (one_pow 1) hfixed
  rw [pow_one] at hc
  refine ⟨c, ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hc
    exact div_ne_zero ht hw hc.symm
  · rw [hc, div_mul_cancel₀ _ hw]

/-- Equal-character binomials on an actual quotient have congruent signed stalk orders. -/
theorem s2v_l1b_divisor_quotient_character_residue
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (β : X ⟶ Y) [IsFinite β.left] [IsDominant β.left]
    (d : X ⟶ X) [IsIso d] (hd : d ≫ β = β)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      d ≫ f = f → ∃! u : Y ⟶ T, β ≫ u = f)
    (τ : X.left.functionField ≃+* X.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      X.left.fromSpecStalk (genericPoint X.left) =
      X.left.fromSpecStalk (genericPoint X.left) ≫ d.left)
    (t w ξ : X.left.functionField) (ht : t ≠ 0) (hw : w ≠ 0) (hξ : ξ ≠ 0)
    (htξ : τ t = ξ * t) (hwξ : τ w = ξ * w)
    (x : Y.left) [UniqueFactorizationMonoid (Y.left.presheaf.stalk x)]
    (A B C D : Y.left.presheaf.stalk x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) (m : ℕ)
    (htm : t ^ m = s2v_l1b_kval_stalkMap (K := X.left.functionField) Y.left x (s2v_l1b_functionFieldPullback β.left) A /
      s2v_l1b_kval_stalkMap (K := X.left.functionField) Y.left x (s2v_l1b_functionFieldPullback β.left) B)
    (hwm : w ^ m = s2v_l1b_kval_stalkMap (K := X.left.functionField) Y.left x (s2v_l1b_functionFieldPullback β.left) C /
      s2v_l1b_kval_stalkMap (K := X.left.functionField) Y.left x (s2v_l1b_functionFieldPullback β.left) D)
    (p : Y.left.presheaf.stalk x) (hp : Prime p) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ))
      (((emultiplicity p C).toNat : ℤ) - ((emultiplicity p D).toNat : ℤ)) := by
  obtain ⟨c, hc0, htc⟩ := s2v_l1b_divisor_quotient_character_ratio X Y β d hd hcat
    τ hτ t w ξ ht hw hξ htξ hwξ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Y.left.presheaf.stalk x) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_div] at hab
    exact hc0 hab.symm
  let ρ := s2v_l1b_kval_stalkMap (K := X.left.functionField) Y.left x (s2v_l1b_functionFieldPullback β.left)
  have hρ : Function.Injective ρ :=
    (s2v_l1b_functionFieldPullback β.left).hom.injective.comp
      (IsFractionRing.injective (Y.left.presheaf.stalk x) Y.left.functionField)
  have htw : t = (ρ a / ρ b) * w := by
    change t = ((s2v_l1b_functionFieldPullback β.left).hom
      (algebraMap _ Y.left.functionField a) /
      (s2v_l1b_functionFieldPullback β.left).hom (algebraMap _ Y.left.functionField b)) * w
    rw [← map_div₀, hab]
    exact htc
  apply s2v_l1b_transport_binomial_rescale ρ hρ hp hA hB hC hD ha0 hb0 m
  rw [← htm, htw, mul_pow, hwm]

end HodgeLean.Foundations.Program
