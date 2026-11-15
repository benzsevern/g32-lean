import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentSelector
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A nonzero binomial coefficient gives unique gcd labels for its complex roots. -/
theorem binomial_root_label
    (g : ℕ) (hg : 0 < g) (κ ζ y : ℂ) (hκ : κ ≠ 0)
    (hζ : IsPrimitiveRoot ζ g) (hy : y ^ g = κ ^ g) :
    ∃! j : ZMod g, y = κ * ζ ^ j.val := by
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  have hr : (y / κ) ^ g = 1 := by
    rw [div_pow, hy]
    exact div_self (pow_ne_zero g hκ)
  obtain ⟨n, hn, he⟩ := hζ.eq_pow_of_pow_eq_one hr
  have hev : y = κ * ζ ^ n := by
    rw [he]
    field_simp
  refine ⟨(n : ZMod g), ?_, ?_⟩
  · simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hn] using hev
  · intro j hj
    apply ZMod.val_injective
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]
    apply hζ.pow_inj (ZMod.val_lt j) hn
    exact mul_left_cancel₀ hκ (hj.symm.trans hev)

/-- Evaluations of the actual integral selector have unique root labels. -/
theorem binomial_selector_evaluation_label
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (g : ℕ) (hg : 0 < g) (ε : A) (q : normalizedChart F)
    (hq : q ^ g = StageTwo.integralCoeff F ε)
    (κ ζ : ℂ) (hκ : κ ≠ 0) (hζ : IsPrimitiveRoot ζ g)
    (ev : normalizedChart F →+* ℂ)
    (hε : ev (StageTwo.integralCoeff F ε) = κ ^ g) :
    ∃! j : ZMod g, ev q = κ * ζ ^ j.val := by
  apply binomial_root_label g hg κ ζ (ev q) hκ hζ
  rw [← map_pow, hq, hε]

end AlgebraicGeometry.RamifiedNormalization.StageFour
