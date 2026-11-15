import HodgeLean.Foundations.QuotientDuality.MonomialWeightedPrincipalUnits
import HodgeLean.Foundations.QuotientDuality.MonomialRescaledEquation
import HodgeLean.Foundations.QuotientDuality.MonomialRescaledFieldGeneration

/-! Removing the exceptional covering power while retaining the strict branch monomial. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem weighted_kummer_generator_strict_reduction
    {R K J : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [Fintype J]
    (hinj : Function.Injective (algebraMap R K))
    (m : ℕ) (hm : 0 < m) (g s : J → R) (hg : ∀ j, g j ≠ 0)
    (α : J → ℕ) (E : R) (u : Rˣ) (v : K)
    (hI : (∏ j, (Ideal.span {g j}) ^ α j) =
      (∏ j, (Ideal.span {s j}) ^ α j) * (Ideal.span {E}) ^ m)
    (hv : v ^ m = algebraMap R K (u : R) * ∏ j, (algebraMap R K (g j)) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤) :
    ∃ (ε : Rˣ) (w : K),
      w ^ m = algebraMap R K (ε : R) * ∏ j, (algebraMap R K (s j)) ^ α j ∧
      Subfield.closure (Set.range (algebraMap R K) ∪ {w}) = ⊤ := by
  obtain ⟨ω, hω⟩ := weighted_principal_product_unit g s α E m hI
  have hprod : (∏ j, g j ^ α j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hg j)
  have hE : E ≠ 0 := by
    intro hz
    apply hprod
    rw [hω, hz, zero_pow hm.ne', mul_zero, mul_zero]
  have hEK : algebraMap R K E ≠ 0 := (map_ne_zero_iff _ hinj).mpr hE
  have hv' : v ^ m = algebraMap R K ((u : R) * ∏ j, g j ^ α j) := by
    simpa only [map_mul, map_prod, map_pow] using hv
  have hq : (u : R) * (∏ j, g j ^ α j) =
      ((u * ω : Rˣ) : R) * ((∏ j, s j ^ α j) * E ^ m) := by
    rw [hω, Units.val_mul, mul_assoc]
  refine ⟨u * ω, v / algebraMap R K E, ?_,
    field_generator_div_coefficient v E hEK hgen⟩
  simpa only [map_prod, map_pow] using
    rescale_kummer_equation m v ((u : R) * ∏ j, g j ^ α j)
      ((u * ω : Rˣ) : R) (∏ j, s j ^ α j) E hv' hq hEK

#print axioms weighted_kummer_generator_strict_reduction
end HodgeLean.Foundations.QuotientDuality
