import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductResidual
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductSquare
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductRootCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportCharacterRoot
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A signed original curve generator supplies a descended reference function and its symmetric coefficient. -/
theorem s2v_l1b_divisor_product_reference
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsIntegral Z.left] [IsIntegral W.left] [IsIntegral B.left]
    [IsProjective Y.hom] [IsProjective Z.hom] [IsProjective W.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hpsurj : Function.Surjective (Point.map p))
    (n : ℕ) (hn : 0 < n)
    [IsIntegral (g3_power Y n).left] [IsIntegral (g3_power Z n).left]
    (q : g3_power Y n ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! b : W ⟶ T, q ≫ b = f)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (β : W ⟶ B) (hβ : q ≫ β = s2_powerMap p n ≫ γ)
    (d : W ⟶ W) (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (κZ : Z.left.functionField ⟶ Y.left.functionField)
    (hκZ : Spec.map κZ ≫ Z.left.fromSpecStalk (genericPoint Z.left) =
      Y.left.fromSpecStalk (genericPoint Y.left) ≫ p.left)
    (τY : Y.left.functionField ≃+* Y.left.functionField)
    (hτY : Spec.map (CommRingCat.ofHom τY.toRingHom) ≫
      Y.left.fromSpecStalk (genericPoint Y.left) =
      Y.left.fromSpecStalk (genericPoint Y.left) ≫ (a (e.symm (.ofAdd (1 : ZMod S.m)))).left)
    (u : Y.left.functionField) (v : Z.left.functionField) (hu : u ≠ 0)
    (hpow : u ^ S.m = κZ.hom v)
    (huchar : τY u = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
      Y.left.germToFunctionField ⊤).hom
        (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * u)
    (τ : W.left.functionField ≃+* W.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d.left) :
    letI : IsDominant q.left := n1bc_dominant_of_points_surjective q hqsurj
    letI : IsDominant γ.left := n1bc_dominant_of_points_surjective γ hγsurj
    letI : IsDominant β.left := n1bc_dominant_of_points_surjective β
      (n1bc_originalCover_points_surjective p hpsurj n q γ hγsurj β hβ)
    ∃ (w : W.left.functionField) (b : B.left.functionField), w ≠ 0 ∧ b ≠ 0 ∧
      s2v_l1b_functionFieldPullback q.left w = s2v_l1b_divisor_product_function Y n u ∧
      s2v_l1b_functionFieldPullback γ.left b = s2v_l1b_divisor_product_function Z n v ∧
      w ^ S.m = s2v_l1b_functionFieldPullback β.left b ∧
      τ w = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W.hom.appTop ≫ W.left.germToFunctionField ⊤).hom
        (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * w := by
  letI : IsDominant p.left := n1bc_dominant_of_points_surjective p hpsurj
  letI : IsDominant q.left := n1bc_dominant_of_points_surjective q hqsurj
  letI : IsDominant γ.left := n1bc_dominant_of_points_surjective γ hγsurj
  letI : IsDominant β.left := n1bc_dominant_of_points_surjective β
    (n1bc_originalCover_points_surjective p hpsurj n q γ hγsurj β hβ)
  letI : IsDominant (s2_powerMap p n).left := n1bc_dominant_of_points_surjective _
    (s2_powerMap_point_surjective p hpsurj n)
  let ζ := Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))
  obtain ⟨χ, hχ⟩ := s2v_l1b_divisor_character_of_primitive_root (NeZero.ne S.m) ζ
    (s2v_l1b_signed_character_primitive S.m (NeZero.ne S.m) s hs)
  have heigen := s2v_l1b_divisor_curve_character_all S Y a e ha1 hamul χ τY hτY u
    (by rw [hχ]; exact huchar)
  obtain ⟨w, hw0, hw⟩ := s2v_l1b_divisor_product_function_quotient S Y W a e ha1 hamul
    n q hqinv hq χ u hu heigen
  have hκeq := s2v_l1b_divisor_generic_map p.left κZ hκZ
  have hpow' : u ^ S.m = s2v_l1b_functionFieldPullback p.left v := by
    simpa only [hκeq] using hpow
  obtain ⟨b, hb0, hb, _⟩ := s2v_l1b_divisor_product_binomial_descent Y Z B p n γ hγinv hγ u v S.m hu hpow'
  refine ⟨w, b, hw0, hb0, hw, hb, ?_, ?_⟩
  · exact s2v_l1b_divisor_product_descended_power Y Z W B p n q γ β hβ u v S.m hpow' w b hw hb
  · letI : IsIso (Spec.map (CommRingCat.ofHom τ.toRingHom)) :=
      (Scheme.Spec.mapIso τ.toCommRingCatIso.op).isIso_hom
    letI : IsDominant (W.left.fromSpecStalk (genericPoint W.left)) := s2_genericPointMorphism_dominant W.left
    haveI : IsDominant (W.left.fromSpecStalk (genericPoint W.left) ≫ d.left) := by
      rw [← hτ]
      infer_instance
    letI : IsDominant d.left := IsDominant.of_comp (W.left.fromSpecStalk (genericPoint W.left)) d.left
    have H := s2v_l1b_divisor_product_residual_character S Y W a e ha1 hamul n hn q d hgen τ hτ χ u heigen w hw
    rw [hχ] at H
    exact H

end HodgeLean.Foundations.Program
