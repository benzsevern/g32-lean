import Mathlib.Algebra.Ring.NonZeroDivisors

/-! Unit transitions between normalized lists of generators. -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Two normalized lists with proportionate regular multiples differ by a unit. -/
theorem g32l4_normalized_generator_transition {A K : Type*} [CommRing A]
    (x y : K → A) (p q : K) (a b : A) (ha : a ∈ nonZeroDivisors A)
    (hp : x p = 1) (hq : y q = 1) (h : ∀ k, a * x k = b * y k) :
    ∃ u : Aˣ, ∀ k, x k = (u : A) * y k := by
  have hb : b = a * x q := by simpa only [hq, mul_one] using (h q).symm
  have he (k : K) : x k = x q * y k := by
    apply (mul_cancel_left_mem_nonZeroDivisors ha).mp
    rw [h k, hb, mul_assoc]
  have hu : x q * y p = 1 := (he p).symm.trans hp
  exact ⟨Units.mkOfMulEqOne (x q) (y p) hu, he⟩

end HodgeLean.Foundations.Program
