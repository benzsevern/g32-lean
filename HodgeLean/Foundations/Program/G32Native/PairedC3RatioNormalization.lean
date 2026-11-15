import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedChartFibre
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring

/-! # Normalized ratios and their marked ideals -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native

/-- Equal branch restrictions along a Cartier slice determine mutually
inverse ratios. Regularity is used to cancel the restricted generator. -/
theorem pairedC3_slice_ratio_inverse {B : Type*} [CommRing B]
    (u v α β : B) (hu : IsRegular u)
    (hv : v = α * u) (huv : u = β * v) : α * β = 1 := by
  apply hu.right
  calc
    (α * β) * u = β * (α * u) := by ring
    _ = β * v := by rw [← hv]
    _ = u := huv.symm
    _ = 1 * u := (one_mul u).symm

/-- A pair of slice restriction coefficients gives an actual unit; a raw
coefficient need not be a constant or equal to one. -/
def pairedC3SliceRatioUnit {B : Type*} [CommRing B]
    (u v α β : B) (hu : IsRegular u)
    (hv : v = α * u) (huv : u = β * v) : Bˣ where
  val := α
  inv := β
  val_inv := pairedC3_slice_ratio_inverse u v α β hu hv huv
  inv_val := by rw [mul_comm]; exact pairedC3_slice_ratio_inverse u v α β hu hv huv

/-- Branch equations modulo the slice ideal determine the unit used in
normalizing the Rees ratio. The coefficient can vary along the base. -/
def pairedC3QuotientSliceRatioUnit {A : Type*} [CommRing A]
    (I : Ideal A) (u v α β : A)
    (hu : IsRegular (Ideal.Quotient.mk I u))
    (hv : v - α * u ∈ I) (huv : u - β * v ∈ I) : (A ⧸ I)ˣ :=
  pairedC3SliceRatioUnit _ _ (Ideal.Quotient.mk I α) (Ideal.Quotient.mk I β) hu
    (by
      apply sub_eq_zero.mp
      rw [← map_mul, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hv)
    (by
      apply sub_eq_zero.mp
      rw [← map_mul, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr huv)

/-- A different lift of the ratio coefficient has the same restriction to
the slice. This is the independence needed before passing to D. -/
theorem pairedC3_slice_ratio_lift_independent {A : Type*} [CommRing A]
    (I : Ideal A) (u v α α' : A)
    (hu : IsRegular (Ideal.Quotient.mk I u))
    (hα : v - α * u ∈ I) (hα' : v - α' * u ∈ I) :
    Ideal.Quotient.mk I α = Ideal.Quotient.mk I α' := by
  apply hu.right
  have h (a : A) (ha : v - a * u ∈ I) :
      Ideal.Quotient.mk I v = Ideal.Quotient.mk I a * Ideal.Quotient.mk I u := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  exact (h α hα).symm.trans (h α' hα')

/-- An invertible slice coefficient remains invertible on the residual
base quotient. Invertibility of the original ambient coefficient is unnecessary. -/
theorem pairedC3_quotient_unit_of_slice_unit
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (J : Ideal A)
    (hJ : RingHom.ker f ≤ J) (a : A) (ha : IsUnit (f a)) :
    IsUnit (Ideal.Quotient.mk J a) := by
  let g := f.liftOfSurjective hf ⟨Ideal.Quotient.mk J, by simpa only [Ideal.mk_ker] using hJ⟩
  have he : g.comp f = Ideal.Quotient.mk J := RingHom.liftOfSurjective_comp f hf _
  have hx : g (f a) = Ideal.Quotient.mk J a :=
    congrArg (fun h : A →+* A ⧸ J => h a) he
  rw [← hx]
  exact ha.map g

/-- Scaling the raw ratio by its invertible slice value changes the marked
ideal from the raw origin to the diagonal intersection. -/
theorem pairedC3_normalized_parameter_ideal {B : Type*} [CommRing B]
    (α : Bˣ) (t : B) :
    Ideal.span {(↑α⁻¹ : B) * t - 1} = Ideal.span {t - ↑α} := by
  have h : (↑α⁻¹ : B) * t - 1 = ↑α⁻¹ * (t - ↑α) := by
    rw [mul_sub, Units.inv_mul]
  rw [h]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    have hm : (↑α : B) * ((↑α⁻¹ : B) * (t - (↑α : B))) ∈
        (Ideal.span {(↑α⁻¹ : B) * (t - (↑α : B))} : Ideal B) :=
      Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    rw [← mul_assoc, Units.mul_inv, one_mul] at hm
    exact hm

/-- The raw origin and the slice fibre are disjoint. Replacing the
normalized marked parameter by the raw ratio would exchange these fibres. -/
theorem pairedC3_raw_origin_disjoint_marked {B : Type*} [CommRing B]
    (α : Bˣ) (t : B) :
    Ideal.span {t} ⊔ Ideal.span {t - (↑α : B)} = ⊤ := by
  let I : Ideal B := Ideal.span {t} ⊔ Ideal.span {t - (↑α : B)}
  change I = ⊤
  apply (Ideal.eq_top_iff_one I).mpr
  have ht : t ∈ I := Ideal.mem_sup_left (Ideal.subset_span rfl)
  have hw : t - (↑α : B) ∈ I := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have ha : (↑α : B) ∈ I := by
    have he : t - (t - (↑α : B)) = (↑α : B) := by ring
    exact he ▸ I.sub_mem ht hw
  simpa only [Units.inv_mul] using I.mul_mem_left (↑α⁻¹ : B) ha

/-- Opposite residual charts give inverse normalized ratios on their overlap. -/
theorem pairedC3_normalized_overlap {B : Type*} [CommRing B]
    (α : Bˣ) (s t : B) (hst : s * t = 1) :
    ((↑α : B) * s) * ((↑α⁻¹ : B) * t) = 1 := by
  calc
    (↑α * s) * (↑α⁻¹ * t) = (↑α * ↑α⁻¹) * (s * t) := by ring
    _ = 1 := by rw [Units.mul_inv, hst, one_mul]

/-- Changes of branch generators cancel against the corresponding change
in the slice value, so the normalized ratio is independent of those units. -/
theorem pairedC3_normalized_generator_change {B : Type*} [CommRing B]
    (α a b : Bˣ) (t : B) :
    (↑(b * a⁻¹ * α)⁻¹ : B) * ((↑b : B) * ↑a⁻¹ * t) = ↑α⁻¹ * t := by
  simp only [mul_inv_rev, inv_inv, Units.val_mul]
  calc
    (↑α⁻¹ * (↑a * ↑b⁻¹)) * (↑b * ↑a⁻¹ * t) =
        ↑α⁻¹ * ((↑a * ↑a⁻¹) * (↑b⁻¹ * ↑b)) * t := by ring
    _ = ↑α⁻¹ * t := by rw [Units.mul_inv, Units.inv_mul, one_mul, mul_one]

/-- Affine translation and scaling turn the slice equation into the
coordinate origin, without replacing its variable unit by a scalar. -/
def pairedC3NormalizedPolynomialEquiv {B : Type*} [CommRing B]
    (α : Bˣ) : B[X] ≃ₐ[B] B[X] :=
  Polynomial.algEquivOfCompEqX
    (C (↑α : B) * (X + 1)) (C (↑α⁻¹ : B) * X - 1)
    (by simp [mul_sub, ← mul_assoc, ← C_mul])
    (by simp [mul_add, ← mul_assoc, ← C_mul])

/-- The corrected parameter maps to the literal origin coordinate under
normalization. This identity retains both the scaling and the translation. -/
theorem pairedC3_normalized_polynomial_parameter {B : Type*} [CommRing B]
    (α : Bˣ) :
    pairedC3NormalizedPolynomialEquiv α (C (↑α⁻¹ : B) * X - 1) = X := by
  change (Polynomial.algEquivOfCompEqX _ _ _ _) _ = _
  simp [Polynomial.algEquivOfCompEqX_apply, mul_add, ← mul_assoc, ← C_mul]

/-- The residual chart comparison sends the corrected slice ideal to
(X - α), retaining the nonconstant slice value α.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem pairedC3_residual_normalized_marked_ideal {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) (α : (A ⧸ J)ˣ) :
    let c := pairedC3ResidualChartBase u v J
    let t := Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)
    Ideal.map (pairedC3ResidualChartEquiv u v J hu hv).toRingHom
      (Ideal.span {c (↑α⁻¹) * t - 1}) =
      Ideal.span {(X : (A ⧸ J)[X]) - C (↑α : A ⧸ J)} := by
  dsimp only
  rw [Ideal.map_span, Set.image_singleton]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_mul,
    map_one, pairedC3_residual_chart_base, pairedC3_residual_chart_ratio]
  exact pairedC3_normalized_parameter_ideal (Units.map (Polynomial.C : (A ⧸ J) →+* (A ⧸ J)[X]).toMonoidHom α) X

/-- The actual residual quotient has a polynomial coordinate in which the
slice parameter w is X. The equivalence keeps the base quotient fixed.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
def pairedC3NormalizedResidualChartEquiv {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) (α : (A ⧸ J)ˣ) :
    (ring u v ⧸ J.map (coeff u v)) ≃+* (A ⧸ J)[X] :=
  (pairedC3ResidualChartEquiv u v J hu hv).trans
    (pairedC3NormalizedPolynomialEquiv α).toRingEquiv

/-- The corrected residual coordinate, including its translation, is the
literal polynomial generator after the normalized chart comparison. -/
theorem pairedC3_normalized_residual_chart_parameter {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) (α : (A ⧸ J)ˣ) :
    pairedC3NormalizedResidualChartEquiv u v J hu hv α
      (pairedC3ResidualChartBase u v J (↑α⁻¹) *
        Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v) - 1) = X := by
  change pairedC3NormalizedPolynomialEquiv α
    (pairedC3ResidualChartEquiv u v J hu hv _) = _
  rw [map_sub, map_mul, map_one, pairedC3_residual_chart_base,
    pairedC3_residual_chart_ratio]
  exact pairedC3_normalized_polynomial_parameter α

#print axioms pairedC3NormalizedResidualChartEquiv
#print axioms pairedC3_normalized_residual_chart_parameter
#print axioms pairedC3_quotient_unit_of_slice_unit
#print axioms pairedC3QuotientSliceRatioUnit
#print axioms pairedC3_slice_ratio_lift_independent
#print axioms pairedC3NormalizedPolynomialEquiv
#print axioms pairedC3_normalized_polynomial_parameter
#print axioms pairedC3_slice_ratio_inverse
#print axioms pairedC3SliceRatioUnit
#print axioms pairedC3_normalized_parameter_ideal
#print axioms pairedC3_raw_origin_disjoint_marked
#print axioms pairedC3_normalized_overlap
#print axioms pairedC3_normalized_generator_change
#print axioms pairedC3_residual_normalized_marked_ideal
end HodgeLean.Foundations.Program.G32Native
