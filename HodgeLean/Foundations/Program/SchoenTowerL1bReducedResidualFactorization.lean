import HodgeLean.Foundations.Program.SchoenTowerL1bRegularTransform
import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A reduced residual equation survives removal of an exceptional parameter regular modulo it. -/
theorem s2v_l1b_residual_regular_equation
    {R : Type*} [CommRing R] (s e : R)
    (hs : (Ideal.span {s}).IsRadical)
    (he : IsRegular (Ideal.Quotient.mk (Ideal.span {s}) e)) :
    PrimeSpectrum.vanishingIdeal
      (closure (PrimeSpectrum.zeroLocus {s * e} \
        PrimeSpectrum.zeroLocus {e})) = Ideal.span {s} := by
  have hsets : PrimeSpectrum.zeroLocus {s * e} \
      PrimeSpectrum.zeroLocus {e} =
      PrimeSpectrum.zeroLocus (Ideal.span {s} : Set R) \
        PrimeSpectrum.zeroLocus (Ideal.span {e} : Set R) := by
    rw [PrimeSpectrum.zeroLocus_singleton_mul, PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.zeroLocus_span]
    exact Set.union_sdiff_right
  rw [hsets, s2v_l1b_divisor_dense_of_minimalPrimes (Ideal.span {s}) (Ideal.span {e})
    (fun q hq hle => s2v_l1b_regular_quotient_avoids_components s e he q hq
      (hle (Ideal.subset_span (Set.mem_singleton e)))),
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hs.radical]

/-- The actual strict transform has the reduced residual equation without a prime divisor assumption. -/
theorem s2v_l1b_strictTransform_reduced_residual_chart
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) (s e : Γ(X, U))
    (hs : (Ideal.span {s}).IsRadical)
    (he : IsRegular (Ideal.Quotient.mk (Ideal.span {s}) e))
    (hD : (D.comap f).ideal U = Ideal.span {s * e})
    (hK : (K.comap f).ideal U = Ideal.span {e}) :
    (s2c_strictTransform f D K).ideal U = Ideal.span {s} := by
  rw [s2v_l1b_strictTransform_affine_formula, hD, hK,
    PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span]
  exact s2v_l1b_residual_regular_equation s e hs he

/-- The selected pair contributes the full exceptional power on a reduced residual chart. -/
theorem s2v_l1b_weighted_reduced_residual_chart
    {X Y : Scheme} (f : X ⟶ Y) (D₁ D₂ K : Y.IdealSheafData)
    (U : X.affineOpens) (s e : Γ(X, U))
    (hs : (Ideal.span {s}).IsRadical)
    (he : IsRegular (Ideal.Quotient.mk (Ideal.span {s}) e))
    (hD₁ : (D₁.comap f).ideal U = Ideal.span {s * e})
    (hD₂ : (D₂.comap f).ideal U = Ideal.span {e})
    (hK : (K.comap f).ideal U = Ideal.span {e})
    (a b m : ℕ) (hab : a + b = m) :
    ((D₁.comap f).ideal U) ^ a * ((D₂.comap f).ideal U) ^ b =
      ((s2c_strictTransform f D₁ K).ideal U) ^ a *
        ((s2c_strictTransform f D₂ K).ideal U) ^ b *
          ((K.comap f).ideal U) ^ m := by
  rw [s2v_l1b_strictTransform_reduced_residual_chart f D₁ K U s e hs he hD₁ hK,
    s2v_l1b_strictTransform_exceptional_chart f D₂ K U (hD₂.trans hK.symm),
    hD₁, hD₂, hK, ← Ideal.span_singleton_mul_span_singleton, mul_pow,
    ← Ideal.one_eq_top, one_pow, mul_one, mul_assoc, ← pow_add, hab]

end HodgeLean.Foundations.Program
