import HodgeLean.Foundations.Program.CompensationCubicSmooth
import HodgeLean.Foundations.Curves.CubicReduced

set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.CompensationCubic
open Polynomial
open scoped TensorProduct

private theorem three_ne_zero' (T : Type*) [CommRing T] [Algebra ℂ T] [IsDomain T] :
    (3 : FractionRing T[X]) ≠ 0 := by
  intro h
  have h' : algebraMap T[X] (FractionRing T[X]) (C (algebraMap ℂ T 3)) = 0 := by
    rw [map_ofNat, map_ofNat, map_ofNat]
    exact h
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), C_eq_zero,
    map_eq_zero_iff _ (algebraMap ℂ T).injective] at h'
  norm_num at h'
open scoped TensorProduct

private theorem two_ne_zero' (T : Type*) [CommRing T] [Algebra ℂ T] [IsDomain T] :
    (2 : FractionRing T[X]) ≠ 0 := by
  intro h
  have h' : algebraMap T[X] (FractionRing T[X]) (C (algebraMap ℂ T 2)) = 0 := by
    rw [map_ofNat, map_ofNat, map_ofNat]
    exact h
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), C_eq_zero,
    map_eq_zero_iff _ (algebraMap ℂ T).injective] at h'
  norm_num at h'
open scoped TensorProduct

theorem isReduced_tensor_zCoordinateRing (T : Type*) [CommRing T] [Algebra ℂ T] [IsDomain T] :
    IsReduced (T ⊗[ℂ] W.toAffine.CoordinateRing) := by
  apply HodgeLean.Foundations.Curves.isReduced_tensor_adjoinRoot W.toAffine.monic_polynomial
  set ι := algebraMap T[X] (FractionRing T[X])
  have hG : ((W.toAffine.polynomial.map (mapRingHom (algebraMap ℂ T))).map ι) =
      X ^ 2 - C (ι (X ^ 3 + 1)) := by
    simp [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W]
  rw [hG]
  apply separable_X_pow_sub_C _ (by exact_mod_cast two_ne_zero' T)
  rw [Ne, map_eq_zero_iff ι (IsFractionRing.injective _ _)]
  intro h
  have := congrArg (Polynomial.coeff · 0) h
  simp at this

private noncomputable def ySwapPolynomial : ℂ[X][X] := X ^ 3 + C (X ^ 3) - C X

private theorem ySwapPolynomial_monic : ySwapPolynomial.Monic := by
  unfold ySwapPolynomial
  monicity!

private theorem ySwap_root : AdjoinRoot.root ySwapPolynomial ^ 3 +
    AdjoinRoot.of ySwapPolynomial X ^ 3 -
      AdjoinRoot.of ySwapPolynomial X = 0 := by
  have h : AdjoinRoot.mk ySwapPolynomial (X ^ 3 + C (X ^ 3) - C X) = 0 :=
    AdjoinRoot.mk_self
  simpa [AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h

private noncomputable def yToSwap : YCoordinateRing →+* AdjoinRoot ySwapPolynomial :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap ℂ (AdjoinRoot ySwapPolynomial))
    (AdjoinRoot.root ySwapPolynomial)) (AdjoinRoot.of ySwapPolynomial X) (by
    simp only [yAffinePolynomial, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      coe_eval₂RingHom]
    linear_combination -ySwap_root)

private noncomputable def swapToY : AdjoinRoot ySwapPolynomial →+* YCoordinateRing :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap ℂ YCoordinateRing)
    (AdjoinRoot.root yAffinePolynomial)) (AdjoinRoot.of yAffinePolynomial X) (by
    have h := yChart_equation
    simp only [ySwapPolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      coe_eval₂RingHom]
    linear_combination -h)

private theorem yToSwap_of_C (c : ℂ) :
    yToSwap (AdjoinRoot.of yAffinePolynomial (C c)) = AdjoinRoot.of ySwapPolynomial (C c) := by
  rw [yToSwap, AdjoinRoot.lift_of]
  simp [AdjoinRoot.algebraMap_eq']

private theorem swapToY_of_C (c : ℂ) :
    swapToY (AdjoinRoot.of ySwapPolynomial (C c)) = AdjoinRoot.of yAffinePolynomial (C c) := by
  rw [swapToY, AdjoinRoot.lift_of]
  simp [AdjoinRoot.algebraMap_eq']

private theorem swapToY_yToSwap : swapToY.comp yToSwap = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [yToSwap_of_C, swapToY_of_C]
    · simp [yToSwap, swapToY]
  · simp [yToSwap, swapToY]

private theorem yToSwap_swapToY : yToSwap.comp swapToY = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [swapToY_of_C, yToSwap_of_C]
    · simp [yToSwap, swapToY]
  · simp [yToSwap, swapToY]

private noncomputable def ySwapEquiv : YCoordinateRing ≃ₐ[ℂ] AdjoinRoot ySwapPolynomial :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom yToSwap swapToY yToSwap_swapToY swapToY_yToSwap) (fun c ↦ by
      change yToSwap (AdjoinRoot.of yAffinePolynomial (C c)) = AdjoinRoot.of ySwapPolynomial (C c)
      exact yToSwap_of_C c)

theorem isReduced_tensor_yCoordinateRing (T : Type*) [CommRing T] [Algebra ℂ T] [IsDomain T] :
    IsReduced (T ⊗[ℂ] YCoordinateRing) := by
  have : IsReduced (T ⊗[ℂ] AdjoinRoot ySwapPolynomial) := by
    apply HodgeLean.Foundations.Curves.isReduced_tensor_adjoinRoot ySwapPolynomial_monic
    set ι := algebraMap T[X] (FractionRing T[X])
    set w : FractionRing T[X] := ι X
    have hG : ((ySwapPolynomial.map (mapRingHom (algebraMap ℂ T))).map ι) =
        X ^ 3 - C (w - w ^ 3) := by
      simp [ySwapPolynomial, w, sub_eq_add_neg] <;> ring
    rw [hG]
    apply separable_X_pow_sub_C _ (by exact_mod_cast three_ne_zero' T)
    dsimp [w]
    rw [← map_pow, ← map_sub]
    apply (map_ne_zero_iff ι (IsFractionRing.injective _ _)).2
    intro h
    have hc := congrArg (Polynomial.coeff · 1) h
    simpa using hc
  exact isReduced_of_injective
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[ℂ] T) ySwapEquiv).toRingEquiv.toRingHom
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[ℂ] T) ySwapEquiv).injective

end HodgeLean.Foundations.Program.CompensationCubic
