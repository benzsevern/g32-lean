import HodgeLean.Foundations.Curves.CubicSmooth

/-! # Reducedness of products of the cubic's chart rings

For a domain `T` over `ℂ`, the rings `T ⊗[ℂ] A` are reduced, where `A` is either affine
coordinate ring of the cubic. Each `A` adjoins a root of a monic polynomial over a polynomial
ring, separable over the fraction field.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Curves

open Polynomial

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

/-- Adjoining a root of a monic polynomial over a domain gives a reduced ring when the
polynomial is separable over the fraction field. -/
theorem isReduced_adjoinRoot_of_separable {D : Type*} [CommRing D] [IsDomain D] {g : D[X]}
    (hg : g.Monic) (hs : (g.map (algebraMap D (FractionRing D))).Separable) :
    IsReduced (AdjoinRoot g) := by
  refine ⟨fun z hz ↦ ?_⟩
  obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  rw [← map_pow, AdjoinRoot.mk_eq_zero] at hn
  rw [AdjoinRoot.mk_eq_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at hn
    exact dvd_trans hn (one_dvd h)
  set ι := algebraMap D (FractionRing D)
  have hinj : Function.Injective ι := IsFractionRing.injective D _
  have h1 : g.map ι ∣ (h.map ι) ^ n := by
    rw [← Polynomial.map_pow]
    exact Polynomial.map_dvd ι hn
  have h2 : g.map ι ∣ h.map ι := (hs.squarefree.dvd_pow_iff_dvd hpos.ne').mp h1
  rw [← modByMonic_eq_zero_iff_dvd hg]
  rw [← modByMonic_eq_zero_iff_dvd (hg.map ι), ← map_modByMonic ι hg] at h2
  exact Polynomial.map_injective ι hinj (by simpa using h2)

/-- Base change of `AdjoinRoot p` to a domain `T`, for monic `p` over `ℂ[X]`, is reduced when the
polynomial stays separable over the fraction field of `T[X]`. -/
theorem isReduced_tensor_adjoinRoot {T : Type*} [CommRing T] [Algebra ℂ T] [IsDomain T]
    {p : ℂ[X][X]} (hp : p.Monic)
    (hs : ((p.map (mapRingHom (algebraMap ℂ T))).map
      (algebraMap T[X] (FractionRing T[X]))).Separable) :
    IsReduced (T ⊗[ℂ] AdjoinRoot p) := by
  let i : ℂ[X] →+* T ⊗[ℂ] ℂ[X] :=
    (Algebra.TensorProduct.includeRight : ℂ[X] →ₐ[ℂ] T ⊗[ℂ] ℂ[X]).toRingHom
  let e₁ := AdjoinRoot.tensorAlgEquiv (R := ℂ) (T := T) p (p.map i) rfl
  let f : T ⊗[ℂ] ℂ[X] ≃ₐ[ℂ] T[X] := (polyEquivTensor ℂ T).symm
  let e₂ := AdjoinRoot.mapAlgEquiv f (p.map i) ((p.map i).map (f : T ⊗[ℂ] ℂ[X] →+* T[X]))
    (Associated.refl _)
  have hfi : (f : T ⊗[ℂ] ℂ[X] →+* T[X]).comp i = mapRingHom (algebraMap ℂ T) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [i, f]
    · simp [i, f]
  have hq : (p.map i).map (f : T ⊗[ℂ] ℂ[X] →+* T[X]) = p.map (mapRingHom (algebraMap ℂ T)) := by
    rw [Polynomial.map_map, hfi]
  have : IsReduced (AdjoinRoot ((p.map i).map (f : T ⊗[ℂ] ℂ[X] →+* T[X]))) := by
    rw [hq]
    exact isReduced_adjoinRoot_of_separable (hp.map _) hs
  exact isReduced_of_injective (e₁.toRingEquiv.trans e₂.toRingEquiv)
    (e₁.toRingEquiv.trans e₂.toRingEquiv).injective

theorem isReduced_tensor_zCoordinateRing (T : Type*) [CommRing T] [Algebra ℂ T] [IsDomain T] :
    IsReduced (T ⊗[ℂ] W.toAffine.CoordinateRing) := by
  apply isReduced_tensor_adjoinRoot W.toAffine.monic_polynomial
  set ι := algebraMap T[X] (FractionRing T[X])
  have hG : ((W.toAffine.polynomial.map (mapRingHom (algebraMap ℂ T))).map ι) =
      X ^ 2 - C (ι (X ^ 3 + X)) := by
    simp [WeierstrassCurve.Affine.polynomial, W, WeierstrassCurve.ofJ1728]
  rw [hG]
  apply separable_X_pow_sub_C _ (by exact_mod_cast two_ne_zero' T)
  rw [Ne, map_eq_zero_iff ι (IsFractionRing.injective _ _)]
  intro h
  have := congrArg (Polynomial.coeff · 1) h
  simp at this

/-- The infinity-chart equation `u³ + v²u - v`, as a monic polynomial in `u` over `ℂ[v]`. -/
private noncomputable def ySwapPolynomial : ℂ[X][X] := X ^ 3 + C (X ^ 2) * X - C X

private theorem ySwapPolynomial_monic : ySwapPolynomial.Monic := by
  unfold ySwapPolynomial
  monicity!

private theorem ySwap_root : AdjoinRoot.root ySwapPolynomial ^ 3 +
    AdjoinRoot.of ySwapPolynomial X ^ 2 * AdjoinRoot.root ySwapPolynomial -
      AdjoinRoot.of ySwapPolynomial X = 0 := by
  have h : AdjoinRoot.mk ySwapPolynomial (X ^ 3 + C (X ^ 2) * X - C X) = 0 :=
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
    apply isReduced_tensor_adjoinRoot ySwapPolynomial_monic
    set ι := algebraMap T[X] (FractionRing T[X])
    set w : FractionRing T[X] := ι X
    have hG : ((ySwapPolynomial.map (mapRingHom (algebraMap ℂ T))).map ι) =
        X ^ 3 + C (w ^ 2) * X - C w := by
      simp [ySwapPolynomial, w]
    rw [hG]
    set d : FractionRing T[X] := -4 * w ^ 6 - 27 * w ^ 2
    have hd : d ≠ 0 := by
      have : d = ι (-4 * X ^ 6 - 27 * X ^ 2) := by simp [d, w, map_ofNat]
      rw [this, Ne, map_eq_zero_iff ι (IsFractionRing.injective _ _)]
      intro h
      have h2 := congrArg (Polynomial.coeff · 2) h
      simp only [coeff_sub, coeff_ofNat_mul, coeff_X_pow, coeff_zero] at h2
      norm_num at h2
      have h27 : algebraMap ℂ T 27 = 0 := by rw [map_ofNat]; exact h2
      rw [map_eq_zero_iff _ (algebraMap ℂ T).injective] at h27
      norm_num at h27
    refine ⟨C d⁻¹ * (C (18 * w ^ 2) * X + C (27 * w)),
      C d⁻¹ * (C (-6 * w ^ 2) * X ^ 2 - C (9 * w) * X - C (4 * w ^ 4)), ?_⟩
    have hdC : C d⁻¹ * C d = (1 : (FractionRing T[X])[X]) := by
      rw [← C_mul, inv_mul_cancel₀ hd, C_1]
    simp only [derivative_sub, derivative_add, derivative_mul, derivative_X_pow, derivative_C,
      derivative_X] at *
    simp only [d, map_mul, map_pow, map_sub, map_neg, map_ofNat, map_natCast] at hdC ⊢
    linear_combination hdC
  exact isReduced_of_injective
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[ℂ] T) ySwapEquiv).toRingEquiv.toRingHom
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[ℂ] T) ySwapEquiv).injective

end HodgeLean.Foundations.Curves
