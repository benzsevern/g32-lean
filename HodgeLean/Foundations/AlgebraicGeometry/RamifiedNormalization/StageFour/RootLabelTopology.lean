import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentLabels
import Mathlib.Topology.Instances.ZMod

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The complex roots of a nonzero binomial coefficient carry the discrete gcd labels. -/
def binomialRootHomeomorph
    (g : ℕ) (hg : 0 < g) (κ ζ : ℂ) (hκ : κ ≠ 0)
    (hζ : IsPrimitiveRoot ζ g) :
    {y : ℂ // y ^ g = κ ^ g} ≃ₜ ZMod g := by
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  let f : ZMod g → {y : ℂ // y ^ g = κ ^ g} := fun j =>
    ⟨κ * ζ ^ j.val, by
      rw [mul_pow, ← pow_mul, Nat.mul_comm j.val g, pow_mul,
        hζ.pow_eq_one, one_pow, mul_one]⟩
  have hinj : Function.Injective f := by
    intro j k he
    have hv : κ * ζ ^ j.val = κ * ζ ^ k.val := congrArg Subtype.val he
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt j) (ZMod.val_lt k) (mul_left_cancel₀ hκ hv)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨j, hj, _⟩ := binomial_root_label g hg κ ζ y.val hκ hζ y.property
    exact ⟨j, Subtype.ext hj.symm⟩
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact (show Continuous e from continuous_of_discreteTopology).homeoOfEquivCompactToT2 |>.symm

end AlgebraicGeometry.RamifiedNormalization.StageFour
