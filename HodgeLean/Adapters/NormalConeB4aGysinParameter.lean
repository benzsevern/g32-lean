import HodgeLean.Adapters.NormalConeB4aDefs
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Regularity of the fibre parameter on flat modules

The fibre parameter acts injectively on a flat module over the polynomial ring.
For an algebra this is multiplication by the equation defining the fibre.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- Flatness makes the equation of every rational fibre act injectively. -/
theorem a3b4a_gysin_parameter_smul_injective
    {k M : Type*} [Field k] [AddCommGroup M] [Module (Polynomial k) M]
    [Module.Flat (Polynomial k) M] (s : k) :
    Function.Injective (fun m : M => (Polynomial.X - Polynomial.C s) • m) := by
  apply smul_right_injective
  exact Polynomial.X_sub_C_ne_zero s

/-- In a flat algebra, multiplication by the fibre equation is injective. -/
theorem a3b4a_gysin_parameter_mul_injective
    {k A : Type*} [Field k] [CommRing A] [Algebra (Polynomial k) A]
    [Module.Flat (Polynomial k) A] (s : k) :
    Function.Injective (fun a : A =>
      (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s)) * a) := by
  simpa only [Algebra.smul_def] using
    (a3b4a_gysin_parameter_smul_injective (M := A) s)

/-- The annihilator of the fibre equation on a flat algebra is zero. -/
theorem a3b4a_gysin_parameter_mul_eq_zero_iff
    {k A : Type*} [Field k] [CommRing A] [Algebra (Polynomial k) A]
    [Module.Flat (Polynomial k) A] (s : k) (a : A) :
    (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s)) * a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    apply a3b4a_gysin_parameter_mul_injective s
    simpa only [mul_zero] using ha
  · rintro rfl
    exact mul_zero _

end HodgeLean.Adapters
