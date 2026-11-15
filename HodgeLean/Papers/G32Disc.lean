import HodgeLean.Papers.G32DiscProofs

/-!
# G32 Theorem A, stage 5: the discriminant `[-2]` (FROZEN SPEC)

This specification isolates the algebraic implication from the explicit determinant
`-2 / 81`, together with invariance under the positive rational rescaling supplied by the
parabolic-polarization comparison, to the discriminant class `[-2]`. It also gives the exact
pointwise output consumed by the transfer datum. Constructing the family and establishing the
comparison premise are outside its scope. HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.RealDefs HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Papers

/-- **The chosen generator is a cube root of unity.** The element
`(-1 + √(-3)) / 2` satisfies the cyclotomic relation used by the explicit matrix certificate.
Source: G32 v0.16, Section 2; the standard presentation of `ℚ(√(-3))`. -/
theorem g32d_zeta_relation :
    let ζ : QuadraticAlgebra ℚ (-3) 0 := (-1 + QuadraticAlgebra.omega) / 2
    ζ ^ 2 + ζ + 1 = 0 :=
  g32d_zeta_relation_aux

example :
    let ζ : QuadraticAlgebra ℚ (-3) 0 := (-1 + QuadraticAlgebra.omega) / 2
    ζ ^ 3 = 1 := by
  dsimp
  have h := g32d_zeta_relation
  dsimp at h
  calc
    ((-1 + QuadraticAlgebra.omega) / 2 : QuadraticAlgebra ℚ (-3) 0) ^ 3
        = (((-1 + QuadraticAlgebra.omega) / 2) ^ 2 +
            (-1 + QuadraticAlgebra.omega) / 2 + 1) *
              ((-1 + QuadraticAlgebra.omega) / 2 - 1) + 1 := by ring
    _ = 1 := by rw [h, zero_mul, zero_add]

/-- **Determinant of the scaled parabolic Gram matrix.** A Gram equality with scale `c`
has determinant `c ^ 6 * (-2 / 81)`.
Source: G32 v0.16, Proposition 6.3; `papers_g32_h0_det`. -/
theorem g32d_gram_det
    {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (c : ℚ) (e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) W)
    (H : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0]
      W →ₗ[QuadraticAlgebra ℚ (-3) 0] QuadraticAlgebra ℚ (-3) 0)
    (hgram : LinearMap.toMatrix₂ e e H =
      (c : QuadraticAlgebra ℚ (-3) 0) •
        g32H0 ((-1 + QuadraticAlgebra.omega) / 2)) :
    (LinearMap.toMatrix₂ e e H).det =
      (c : QuadraticAlgebra ℚ (-3) 0) ^ 6 * (-2 / 81) :=
  g32d_gram_det_aux c e H hgram

example {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) W)
    (H : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0]
      W →ₗ[QuadraticAlgebra ℚ (-3) 0] QuadraticAlgebra ℚ (-3) 0)
    (hgram : LinearMap.toMatrix₂ e e H =
      g32H0 ((-1 + QuadraticAlgebra.omega) / 2)) :
    (LinearMap.toMatrix₂ e e H).det = -2 / 81 := by
  simpa using g32d_gram_det 1 e H (by simpa using hgram)

/-- **Positive rescaling preserves the explicit discriminant class.** The determinant of
`c • g32H0` is `c ^ 6 * (-2 / 81)`. Its sixth-power factor is the norm of the rational element
`c ^ 3`, while `[-2 / 81] = [-2]` because `81` is a norm.
Source: G32 v0.16, Section 6 and Proposition 6.3; F-1569 (1); van Geemen, LNM 1594, §5. -/
theorem g32d_scaled_det_class (c : ℚ) (hc : 0 < c) :
    ((Units.mk0 ((-2 / 81 : ℚ) * c ^ 6) (mul_ne_zero (by norm_num)
      (pow_ne_zero 6 (ne_of_gt hc))) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) = classNegTwo :=
  g32d_scaled_det_class_aux c hc

example :
    ((Units.mk0 ((-2 / 81 : ℚ) * (2 : ℚ) ^ 6) (by norm_num) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) = classNegTwo :=
  g32d_scaled_det_class 2 (by norm_num)

/-- **Stage-5 bridge.** If every fibre has the parabolic-polarization comparison, then every
fibre has the discriminant class required by `G32TransferDatum.fiber_disc`.
Source: G32 v0.16, Section 6 and Proposition 6.3. -/
theorem g32d_fiber_disc {S : Type} (fiber : S → g32t_Sixfold)
    (fiber_polarized : ∀ s, g32t_PolarizedWeil (fiber s))
    (hpar : ∀ s, g32d_ParabolicPolarization (fiber_polarized s)) :
    ∀ s, g32t_disc (fiber_polarized s) = classNegTwo :=
  g32d_fiber_disc_aux fiber fiber_polarized hpar

example {S : Type} (fiber : S → g32t_Sixfold)
    (fiber_polarized : ∀ s, g32t_PolarizedWeil (fiber s))
    (hpar : ∀ s, g32d_ParabolicPolarization (fiber_polarized s)) :
    ∀ s, g32t_disc (fiber_polarized s) = classNegTwo :=
  g32d_fiber_disc fiber fiber_polarized hpar

end HodgeLean.Papers
