import HodgeLean.Foundations.Program.SchoenTowerL1bInvertibleIdeal
import HodgeLean.Foundations.Program.SchoenTowerI2bChartAlgebra
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! The coefficient charts of an actual rank-one centre ideal.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Making a selected coefficient invertible gives a chart ratio after any ring map.
Source: the coefficient identity in a free rank-one ideal and unit cancellation. -/
theorem s2v_i2b_invertible_ideal_localized_ratio
    {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ I)
    (e : I ≃ₗ[R] R) (f : R →+* A) (hunit : IsUnit (f (e ⟨v, hv⟩))) :
    ∃ s : A, f u = s * f v := by
  let ui : I := ⟨u, hu⟩
  let vi : I := ⟨v, hv⟩
  have hcrossI : e ui • vi = e vi • ui := by
    apply e.injective
    simp only [map_smul, smul_eq_mul, mul_comm]
  have hcross : f (e ui) * f v = f (e vi) * f u := by
    simpa only [SetLike.val_smul, smul_eq_mul, map_mul] using congrArg f (congrArg Subtype.val hcrossI)
  obtain ⟨w, hw⟩ := hunit
  refine ⟨f (e ui) * ↑w⁻¹, ?_⟩
  symm
  calc
    (f (e ui) * ↑w⁻¹) * f v = ↑w⁻¹ * (f (e ui) * f v) := by ring
    _ = ↑w⁻¹ * (f (e vi) * f u) := by rw [hcross]
    _ = f u := by rw [← hw, ← mul_assoc, Units.inv_mul, one_mul]

end HodgeLean.Foundations.Program
