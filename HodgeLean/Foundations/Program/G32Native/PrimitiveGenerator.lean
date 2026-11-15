import HodgeLean.Foundations.Program.SchoenTransferCurveGeneratorEigenspace
import HodgeLean.Foundations.Program.G32Native.PrimitiveCharacters
import HodgeLean.Foundations.Program.SchoenTransferForwardScalar

/-! # The residual generator on the linear primitive comparison -/
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit
attribute [local irreducible] cupProductOf homPullback

/-- Forward pullback corresponds to the inverse cyclotomic scalar on the supplied linear comparison. -/
theorem primitive_forward_scalar
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d : ℕ)
    (b : V ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (F : V →ₗ[ℚ] HQ Y 1)
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (F v) =
        F (cyc_scalar b (g32p_fieldValue S u) v)) :
    ∀ v, homPullback (a (e.symm (.ofAdd 1))) 1 (F v) =
      F (cyc_scalar b (IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))⁻¹ v) := by
  let ζ := IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m)
  let δ := e.symm (Multiplicative.ofAdd 1)
  let D := homPullback (a δ) 1
  let B := homPullback (a δ⁻¹) 1
  let T := cyc_scalar b ζ
  let Ti := cyc_scalar b ζ⁻¹
  obtain ⟨u, hu⟩ := S.surjective (Multiplicative.ofAdd 1)
  have huq : QuotientGroup.mk u = δ := by
    apply e.injective
    rw [he, hu]
    exact (e.apply_symm_apply _).symm
  have hfu : g32p_fieldValue S u = ζ := by
    simp only [g32p_fieldValue, hu, toAdd_ofAdd,
      ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
    rfl
  have hDB : D.comp B = LinearMap.id := by
    dsimp only [D, B]
    rw [← spec_homPullback_comp, ← hamul, mul_inv_cancel, ha1, spec_homPullback_id]
  have hTi : T.comp Ti = LinearMap.id := by
    change cyc_rep b ζ * cyc_rep b ζ⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ ((IsCyclotomicExtension.zeta_spec S.m ℚ
      (cyc_Field S.m)).ne_zero (by have := S.three_le; omega)), map_one]
  intro v
  have hs := hscalar u (Ti v)
  rw [huq, hfu] at hs
  have ht := congrArg D hs
  change D (B (F (Ti v))) = D (F (T (Ti v))) at ht
  rw [← LinearMap.comp_apply D B, hDB, LinearMap.id_apply,
    ← LinearMap.comp_apply T Ti, hTi, LinearMap.id_apply] at ht
  exact ht.symm

#print axioms primitive_forward_scalar
/-- The forward generator eigenspace is the transported intrinsic character space. -/
theorem primitive_generator_eigenspace
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d : ℕ)
    (b : V ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (F : V →ₗ[ℚ] HQ Y 1) (hf : Function.Injective F)
    (himage : LinearMap.range F = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (F v) =
        F (cyc_scalar b (g32p_fieldValue S u) v)) :
    ∀ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      s4_e2_curveSpace S Y a e t = Module.End.eigenspace
        ((homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ)
        (t ((IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))⁻¹)) := by
  intro t
  let ζ := IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m)
  let Fc := F.baseChange ℂ
  let A := (homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ
  let T := (cyc_scalar b ζ⁻¹).baseChange ℂ
  let Q := (Polynomial.cyclotomic S.m ℚ).map (algebraMap ℚ ℂ)
  have hζ : IsPrimitiveRoot ζ⁻¹ S.m := (IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)).inv
  have hF : Function.Injective Fc := Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hr : LinearMap.range Fc = LinearMap.ker (Polynomial.aeval A Q) := by
    dsimp only [Fc, A, Q]
    rw [s4_baseChange_range, himage, ← ker_baseChange, baseChange_aeval]
  have hFA : ∀ x, A (Fc x) = Fc (T x) := by
    have hh : homPullback (a (e.symm (.ofAdd 1))) 1 ∘ₗ F =
        F ∘ₗ cyc_scalar b ζ⁻¹ :=
      LinearMap.ext (primitive_forward_scalar S Y a e he ha1 hamul d b F hscalar)
    have hb := congrArg (LinearMap.baseChange ℂ) hh
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hb
    exact LinearMap.congr_fun hb
  have hroot : Q.IsRoot (t ζ⁻¹) := by
    dsimp only [Q]
    rw [Polynomial.map_cyclotomic]
    exact Polynomial.isRoot_cyclotomic_iff.mpr (hζ.map_of_injective t.injective)
  have ht := primitive_character_map S Y a e d b F hf himage hscalar t
  change (cyc_eigenspace b t).map Fc = s4_e2_curveSpace S Y a e t at ht
  rw [← ht, s4_cyclotomic_eigenspace_primitive_generator b t ζ⁻¹ hζ]
  exact s4_eigenspace_map_of_polynomial_range Fc T A Q hF hFA hr (t ζ⁻¹) hroot

#print axioms primitive_generator_eigenspace
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
