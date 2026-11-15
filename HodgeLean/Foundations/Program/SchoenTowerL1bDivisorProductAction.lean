import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductSymmetry
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportConstants

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Pullback of a coordinate product along an actual coordinate action is computed factorwise. -/
theorem s2v_l1b_divisor_product_function_action
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    [∀ g, IsDominant (a g).left]
    (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n))
    [IsDominant (s2_action S Y a e n v σ).left] (u : Y.left.functionField) :
    letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
      s2v_l1b_divisor_projection_dominant Y n
    s2v_l1b_functionFieldPullback (s2_action S Y a e n v σ).left
      (s2v_l1b_divisor_product_function Y n u) =
        ∏ j, s2v_l1b_functionFieldPullback (g3_proj Y n (σ.symm j)).left
          (s2v_l1b_functionFieldPullback (a (e.symm (.ofAdd (v j)))).left u) := by
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  unfold s2v_l1b_divisor_product_function
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  have hj : (s2_action S Y a e n v σ).left ≫ (g3_proj Y n j).left =
      (g3_proj Y n (σ.symm j)).left ≫ (a (e.symm (.ofAdd (v j)))).left :=
    congrArg Over.Hom.left (s2_check_lift_proj n _ j)
  have H := s2v_l1b_divisor_functionFieldPullback_congr _ _ hj
  rw [s2v_l1b_functionFieldPullback_comp, s2v_l1b_functionFieldPullback_comp] at H
  exact congrArg (fun k : Y.left.functionField ⟶ (g3_power Y n).left.functionField => k u) H

/-- Coordinate eigenvalues multiply in the actual field of the power. -/
theorem s2v_l1b_divisor_product_function_eigenvalues
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    [∀ g, IsDominant (a g).left]
    (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n))
    [IsDominant (s2_action S Y a e n v σ).left]
    (u : Y.left.functionField) (c : Fin n → ℂ)
    (heigen : ∀ j,
      s2v_l1b_functionFieldPullback (a (e.symm (.ofAdd (v j)))).left u =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
          Y.left.germToFunctionField ⊤).hom (c j) * u) :
    s2v_l1b_functionFieldPullback (s2_action S Y a e n v σ).left
      (s2v_l1b_divisor_product_function Y n u) =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ (g3_power Y n).hom.appTop ≫
          (g3_power Y n).left.germToFunctionField ⊤).hom (∏ j, c j) *
            s2v_l1b_divisor_product_function Y n u := by
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  let cY : CommRingCat.of ℂ ⟶ Y.left.functionField :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫ Y.left.germToFunctionField ⊤
  let cP : CommRingCat.of ℂ ⟶ (g3_power Y n).left.functionField :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ (g3_power Y n).hom.appTop ≫
      (g3_power Y n).left.germToFunctionField ⊤
  have hc (j : Fin n) :
      s2v_l1b_functionFieldPullback (g3_proj Y n (σ.symm j)).left (cY.hom (c j)) =
        cP.hom (c j) := by
    have H : cY ≫ s2v_l1b_functionFieldPullback (g3_proj Y n (σ.symm j)).left = cP := by
      apply s2v_l1b_generic_constants
      rw [s2v_l1b_functionFieldPullback_generic_square, Category.assoc, Over.w]
    exact congrArg (fun k : CommRingCat.of ℂ ⟶ (g3_power Y n).left.functionField => k.hom (c j)) H
  rw [s2v_l1b_divisor_product_function_action]
  change _ = cP.hom (∏ j, c j) * _
  simp_rw [heigen, map_mul]
  change (∏ j, s2v_l1b_functionFieldPullback (g3_proj Y n (σ.symm j)).left
    (cY.hom (c j)) * s2v_l1b_functionFieldPullback (g3_proj Y n (σ.symm j)).left u) = _
  simp_rw [hc]
  rw [Finset.prod_mul_distrib, ← map_prod]
  congr 1
  exact Equiv.prod_comp σ.symm (fun j => s2v_l1b_functionFieldPullback (g3_proj Y n j).left u)

/-- The sum-zero coordinate action fixes a product of functions with the same character. -/
theorem s2v_l1b_divisor_product_function_sum_zero
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    [∀ g, IsDominant (a g).left]
    (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n))
    [IsDominant (s2_action S Y a e n v σ).left]
    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (u : Y.left.functionField)
    (heigen : ∀ g, s2v_l1b_functionFieldPullback (a g).left u =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
        Y.left.germToFunctionField ⊤).hom (χ (e g) : ℂ) * u)
    (hv : ∑ j, v j = 0) :
    s2v_l1b_functionFieldPullback (s2_action S Y a e n v σ).left
      (s2v_l1b_divisor_product_function Y n u) =
        s2v_l1b_divisor_product_function Y n u := by
  have H := s2v_l1b_divisor_product_function_eigenvalues S Y a e n v σ u
    (fun j => (χ (.ofAdd (v j)) : ℂ)) (fun j => by
      simpa only [e.apply_symm_apply] using heigen (e.symm (.ofAdd (v j))))
  have hprod : (∏ j, (χ (.ofAdd (v j)) : ℂ)) = 1 := by
    change (∏ j, Units.coeHom ℂ (χ (.ofAdd (v j)))) = 1
    rw [← map_prod (Units.coeHom ℂ), ← map_prod χ,
      ← ofAdd_sum, hv]
    exact map_one ((Units.coeHom ℂ).comp χ)
  rw [hprod, map_one, one_mul] at H
  exact H

/-- The total coordinate character is the character evaluated at the sum of the translations. -/
theorem s2v_l1b_divisor_product_function_character
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    [∀ g, IsDominant (a g).left]
    (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n))
    [IsDominant (s2_action S Y a e n v σ).left]
    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (u : Y.left.functionField)
    (heigen : ∀ g, s2v_l1b_functionFieldPullback (a g).left u =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
        Y.left.germToFunctionField ⊤).hom (χ (e g) : ℂ) * u) :
    s2v_l1b_functionFieldPullback (s2_action S Y a e n v σ).left
      (s2v_l1b_divisor_product_function Y n u) =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ (g3_power Y n).hom.appTop ≫
          (g3_power Y n).left.germToFunctionField ⊤).hom
            (χ (.ofAdd (∑ j, v j)) : ℂ) * s2v_l1b_divisor_product_function Y n u := by
  have H := s2v_l1b_divisor_product_function_eigenvalues S Y a e n v σ u
    (fun j => (χ (.ofAdd (v j)) : ℂ)) (fun j => by
      simpa only [e.apply_symm_apply] using heigen (e.symm (.ofAdd (v j))))
  have hprod : (∏ j, (χ (.ofAdd (v j)) : ℂ)) = (χ (.ofAdd (∑ j, v j)) : ℂ) := by
    change (∏ j, Units.coeHom ℂ (χ (.ofAdd (v j)))) = _
    rw [← map_prod (Units.coeHom ℂ), ← map_prod χ, ← ofAdd_sum]
    rfl
  rw [hprod] at H
  exact H

end HodgeLean.Foundations.Program
