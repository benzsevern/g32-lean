import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RootLabelEvaluation
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The zero fibre of a weighted power projection contains exactly one point for each retained label. -/
def weightedPowerZeroFibreEquiv
    (g n : ℕ) (hn : 0 < n) (k : ZMod g → ℂ) (hk : ∀ j, k j ≠ 0) :
    {z : ZMod g × ℂ // k z.1 * z.2 ^ n = 0} ≃ ZMod g where
  toFun := fun z => z.val.1
  invFun := fun j => ⟨(j, 0), by rw [zero_pow (Nat.ne_of_gt hn), mul_zero]⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    have hz : z.val.2 ^ n = 0 := (mul_eq_zero.mp z.property).resolve_left (hk z.val.1)
    exact (eq_zero_of_pow_eq_zero hz).symm
  right_inv := fun _ => rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
