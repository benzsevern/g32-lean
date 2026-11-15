import HodgeLean.Foundations.Program.G32SelectedRealizationCyclotomic

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- An inverse operator satisfies the same cyclotomic relation. -/
theorem s0_cyclotomic_inverse_relation {m : ℕ} [NeZero m]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T U : Module.End ℚ V) (hTU : T * U = 1)
    (hT : Polynomial.aeval T (Polynomial.cyclotomic m ℚ) = 0) :
    Polynomial.aeval U (Polynomial.cyclotomic m ℚ) = 0 := by
  obtain ⟨ρ, hρ⟩ := g32y_cyclotomic_action T hT
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  have hz : ζ ≠ 0 := (IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)).ne_zero (NeZero.ne m)
  have hu : U = ρ ζ⁻¹ := by
    calc
      U = 1 * U := (one_mul _).symm
      _ = (ρ ζ⁻¹ * T) * U := by rw [← hρ, ← map_mul, inv_mul_cancel₀ hz, map_one]
      _ = ρ ζ⁻¹ := by rw [mul_assoc, hTU, mul_one]
  have hzroot : Polynomial.aeval ζ⁻¹ (Polynomial.cyclotomic m ℚ) = 0 := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat
      (IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)).inv (NeZero.pos m)]
    exact minpoly.aeval ℚ ζ⁻¹
  rw [hu, Polynomial.aeval_algHom_apply, hzroot, map_zero]

#print axioms s0_cyclotomic_inverse_relation
end HodgeLean.Foundations.Program
