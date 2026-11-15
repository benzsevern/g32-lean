import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-! # Independence of the normalized paired ratio modulo the original ideal -/
namespace HodgeLean.Foundations.Program.G32Native
variable {B : Type*} [CommRing B]

/-- A change of divisor equations and a change of lift of their ratio
preserve the normalized ratio modulo the pulled-back slice ideal.
The displayed multiplicative identity retains the orientation `ratio - 1`.
Source: Hartshorne, Algebraic Geometry, II.7, affine blow-up charts. -/
theorem paired_c3_normalized_ratio_change
    (I : Ideal B) (ρ ρ' c z z' : B) (hunit : IsUnit ρ')
    (hlift : ρ' - c * ρ ∈ I)
    (hchart : ρ' * (1 + z') = c * ρ * (1 + z)) :
    z' - z ∈ I := by
  have he : ρ' * (z' - z) = -(ρ' - c * ρ) * (1 + z) := by
    calc
      ρ' * (z' - z) = ρ' * (1 + z') - ρ' * (1 + z) := by ring
      _ = c * ρ * (1 + z) - ρ' * (1 + z) := by rw [hchart]
      _ = -(ρ' - c * ρ) * (1 + z) := by ring
  have hm : ρ' * (z' - z) ∈ I := by
    rw [he]
    exact I.mul_mem_right _ (I.neg_mem hlift)
  rcases hunit with ⟨u, rfl⟩
  have h := I.mul_mem_left (↑u⁻¹ : B) hm
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using h

/-- Consequently the normalized generators agree in the actual quotient
by the pulled-back ideal, before passing to the conormal cokernel. -/
theorem paired_c3_normalized_ratio_quotient
    (I : Ideal B) (ρ ρ' c z z' : B) (hunit : IsUnit ρ')
    (hlift : ρ' - c * ρ ∈ I)
    (hchart : ρ' * (1 + z') = c * ρ * (1 + z)) :
    Ideal.Quotient.mk I z' = Ideal.Quotient.mk I z := by
  apply Ideal.Quotient.eq.mpr
  exact paired_c3_normalized_ratio_change I ρ ρ' c z z' hunit hlift hchart

end HodgeLean.Foundations.Program.G32Native
