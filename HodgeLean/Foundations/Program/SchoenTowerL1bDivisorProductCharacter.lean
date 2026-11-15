import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCharacterPowers
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalAction
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportConstants

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A generator eigenvalue extends to the full curve character along the retained cyclic equivalence. -/
theorem s2v_l1b_divisor_curve_character_all
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (χ : Multiplicative (ZMod S.m) →* ℂˣ)
    (τ : Y.left.functionField ≃+* Y.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Y.left.fromSpecStalk (genericPoint Y.left) =
      Y.left.fromSpecStalk (genericPoint Y.left) ≫
        (a (e.symm (.ofAdd (1 : ZMod S.m)))).left)
    (u : Y.left.functionField)
    (hu : τ u = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
      Y.left.germToFunctionField ⊤).hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ) * u)
    (g : S.H ⧸ S.χ.ker) :
    letI : IsIso (a g) :=
      (s2v_l1b_divisor_original_action S Y a ha1 hamul g).asIso.isIso_hom
    s2v_l1b_functionFieldPullback (a g).left u =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
        Y.left.germToFunctionField ⊤).hom (χ (e g) : ℂ) * u := by
  letI : IsIso (a g) :=
    (s2v_l1b_divisor_original_action S Y a ha1 hamul g).asIso.isIso_hom
  let cY : CommRingCat.of ℂ ⟶ Y.left.functionField :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫ Y.left.germToFunctionField ⊤
  let g₀ := e.symm (.ofAdd (1 : ZMod S.m))
  let k := (e g).toAdd.val
  have hgp : g₀ ^ k = g := by
    apply e.injective
    rw [map_pow, show e g₀ = .ofAdd (1 : ZMod S.m) from e.apply_symm_apply _]
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
    exact congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val (e g).toAdd)
  let ξ := cY.hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ)
  have hconstants := s2v_l1b_generic_constants Y Y (CommRingCat.ofHom τ.toRingHom) (by
    rw [hτ, Category.assoc, Over.w])
  have hξ : τ ξ = ξ :=
    congrArg (fun f : CommRingCat.of ℂ ⟶ Y.left.functionField =>
      f.hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ)) hconstants
  have H := s2v_l1b_divisor_character_power Y (S.H ⧸ S.χ.ker) a ha1 hamul
    g₀ τ hτ u ξ hξ hu k
  let η : Multiplicative (ZMod S.m) →* Y.left.functionField :=
    cY.hom.toMonoidHom.comp ((Units.coeHom ℂ).comp χ)
  have hscalar : ξ ^ k = cY.hom (χ (e g) : ℂ) := by
    change ξ ^ k = η (e g)
    rw [show ξ = η (e g₀) by
      change cY.hom (χ (.ofAdd (1 : ZMod S.m)) : ℂ) = cY.hom (χ (e g₀) : ℂ)
      rw [show e g₀ = .ofAdd (1 : ZMod S.m) from e.apply_symm_apply _]]
    rw [← map_pow, ← map_pow, hgp]
  simpa only [hgp, hscalar] using H

end HodgeLean.Foundations.Program
