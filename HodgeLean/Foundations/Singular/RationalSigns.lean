import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! Evaluation of the integral signs of rational chain complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Singular

/-- The unit-valued tensor-complex sign evaluates as the rational Koszul sign.
Source: Hatcher, Algebraic Topology, §3.2, the differential of a tensor complex. -/
theorem rational_sign_apply {V W : ModuleCat ℚ} (f : V ⟶ W) (p : ℕ) (z : V) :
    (((-1 : ℤˣ) ^ p) • f).hom z = (-1 : ℚ) ^ p • f.hom z := by
  change ((((-1 : ℤ) ^ p) • f).hom z) = _
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℚ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

#print axioms rational_sign_apply
end HodgeLean.Foundations.Singular
