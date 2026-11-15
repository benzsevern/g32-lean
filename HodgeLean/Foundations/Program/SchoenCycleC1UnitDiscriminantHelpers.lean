import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Integral closure from a power basis with unit discriminant -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An integral power generator with discriminant a base-ring unit generates
the entire integral closure in its separable field extension. -/
theorem s2e_c1_integralClosure_eq_adjoin_of_unit_discriminant
    {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] (B : PowerBasis K L)
    (hint : IsIntegral R B.gen) (d : Rˣ)
    (hd : Algebra.discr K B.basis = algebraMap R K (d : R)) :
    integralClosure R L = Algebra.adjoin R ({B.gen} : Set L) := by
  letI : Module.Finite K L := B.finite
  apply le_antisymm
  · intro z hz
    have h := Algebra.discr_mul_isIntegral_mem_adjoin K (B := B) hint hz
    rw [hd, algebraMap_smul] at h
    have h' := (Algebra.adjoin R ({B.gen} : Set L)).smul_mem h (↑(d⁻¹) : R)
    simpa only [smul_smul, Units.inv_mul, one_smul] using h'
  · apply Algebra.adjoin_le
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hint

/-- An element of the fraction field and its integral inverse come from a
unit of the integrally closed base ring. -/
theorem s2e_c1_unit_of_integral_inverse
    {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (t : K) (ht : t ≠ 0) (hi : IsIntegral R t) (hinv : IsIntegral R t⁻¹) :
    ∃ d : Rˣ, algebraMap R K (d : R) = t := by
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hinv
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, hx, hy, mul_inv_cancel₀ ht, map_one]
  exact ⟨Units.mkOfMulEqOne x y hxy, hx⟩

/-- Integrality of the inverse derivative forces the power-basis
discriminant to be a unit in the normal base ring. -/
theorem s2e_c1_discriminant_unit_of_integral_inverse_derivative
    {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] (B : PowerBasis K L)
    (hint : IsIntegral R B.gen)
    (hinv : IsIntegral R (Polynomial.aeval B.gen (minpoly K B.gen).derivative)⁻¹) :
    ∃ d : Rˣ, Algebra.discr K B.basis = algebraMap R K (d : R) := by
  letI : Module.Finite K L := B.finite
  have hi : IsIntegral R (Algebra.discr K B.basis) :=
    Algebra.discr_isIntegral K (fun i => by
      rw [B.basis_eq_pow]
      exact hint.pow i.val)
  have hii : IsIntegral R (Algebra.discr K B.basis)⁻¹ := by
    rw [Algebra.discr_powerBasis_eq_norm K B, mul_inv_rev, ← Algebra.norm_inv]
    exact (Algebra.isIntegral_norm K hinv).mul
      (by simpa only [← inv_pow, inv_neg, inv_one] using
        ((isIntegral_one : IsIntegral R (1 : K)).neg).pow (Module.finrank K L * (Module.finrank K L - 1) / 2))
  obtain ⟨d, hd⟩ := s2e_c1_unit_of_integral_inverse
    (Algebra.discr K B.basis) (Algebra.discr_not_zero_of_basis K B.basis) hi hii
  exact ⟨d, hd.symm⟩

end HodgeLean.Foundations.Program
