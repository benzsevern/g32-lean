import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportQuotientAction

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The descended coordinate product has the specified residual generator character. -/
theorem s2v_l1b_divisor_product_residual_character
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsIntegral W.left] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (hn : 0 < n) [IsIntegral (g3_power Y n).left]
    (q : g3_power Y n ⟶ W) [IsDominant q.left]
    (d : W ⟶ W) [IsDominant d.left]
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (τ : W.left.functionField ≃+* W.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d.left)
    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (u : Y.left.functionField)
    (heigen : ∀ g,
      letI : IsIso (a g) :=
        (s2v_l1b_divisor_original_action S Y a ha1 hamul g).asIso.isIso_hom
      s2v_l1b_functionFieldPullback (a g).left u =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
          Y.left.germToFunctionField ⊤).hom (χ (e g) : ℂ) * u)
    (w : W.left.functionField)
    (hw : s2v_l1b_functionFieldPullback q.left w = s2v_l1b_divisor_product_function Y n u) :
    τ w = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W.hom.appTop ≫
      W.left.germToFunctionField ⊤).hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ) * w := by
  letI : ∀ g, IsIso (a g) := fun g =>
    (s2v_l1b_divisor_original_action S Y a ha1 hamul g).asIso.isIso_hom
  let D := s2_action S Y a e n (s2_delta S n hn 1) 1
  letI : IsIso D := (s2_coordinateActionIso S Y a e ha1 hamul n (s2_delta S n hn 1) 1).isIso_hom
  have H := s2v_l1b_divisor_product_function_character S Y a e n (s2_delta S n hn 1) 1 χ u heigen
  rw [s2_check_delta_sum] at H
  let cW : CommRingCat.of ℂ ⟶ W.left.functionField :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ W.hom.appTop ≫ W.left.germToFunctionField ⊤
  have hconstants := s2v_l1b_generic_constants W (g3_power Y n)
    (s2v_l1b_functionFieldPullback q.left) (by
      rw [s2v_l1b_functionFieldPullback_generic_square, Category.assoc, Over.w])
  have hc := congrArg (fun f : CommRingCat.of ℂ ⟶ (g3_power Y n).left.functionField =>
    f.hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ)) hconstants
  apply (s2v_l1b_functionFieldPullback q.left).hom.injective
  change s2v_l1b_functionFieldPullback q.left (τ.toRingHom w) =
    s2v_l1b_functionFieldPullback q.left (cW.hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ) * w)
  calc
    _ = s2v_l1b_functionFieldPullback D.left (s2v_l1b_functionFieldPullback q.left w) :=
      (s2v_l1b_transport_quotient_field_action q.left D.left d.left
        (congrArg Over.Hom.left hgen) τ.toRingHom hτ w).symm
    _ = _ := by
      rw [hw, map_mul, hw]
      rw [H]
      exact congrArg (fun z => z * s2v_l1b_divisor_product_function Y n u) hc.symm

end HodgeLean.Foundations.Program
