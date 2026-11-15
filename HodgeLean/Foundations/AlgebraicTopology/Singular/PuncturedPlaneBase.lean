import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.CompactOpen
import HodgeLean.Adapters.HolomorphicPeriodsCocycleProofs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass

/-! Base objects for integral punctured-plane degree.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace AlgebraicTopology.Singular.PuncturedPlane

/-- Exponential circle with specified initial logarithm and integral turns.
Source: Hatcher, Algebraic Topology (2002), §1.1. -/
def windingCircle (c : ℂ) (k : ℤ) :
    C(UnitAddCircle, {z : ℂ // z ≠ 0}) := by
  let f : ℝ → {z : ℂ // z ≠ 0} := fun s =>
    ⟨Complex.exp (c + (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I))),
      Complex.exp_ne_zero _⟩
  have hf : Continuous f := (Complex.continuous_exp.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).subtype_mk _
  have hp : Function.Periodic f 1 := by
    intro s
    apply Subtype.ext
    change Complex.exp (c + ((s + 1 : ℝ) : ℂ) * _) = Complex.exp (c + (s : ℂ) * _)
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul,
      ← add_assoc, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  exact ⟨hp.lift, hf.quotient_lift _⟩

example (s : ℝ) : (windingCircle 0 1 (s : UnitAddCircle)).val =
    Complex.exp (0 + (s : ℂ) * ((1 : ℤ) * (2 * Real.pi * Complex.I))) := rfl

end AlgebraicTopology.Singular.PuncturedPlane
