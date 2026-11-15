import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistLinearMonomial

/-! # Actual coordinate indices for homogeneous degree-one polynomial data -/

noncomputable section
set_option maxHeartbeats 400000
open ProjSpaceCech
namespace HodgeLean.Foundations.Program.G32Native

/-- The degree-one monomial of the specified original coordinate. -/
def paired_twist_coordinateMonomial (n : ℕ) (i : Fin (n + 1)) : Twist.Mon n 1 ∅ := by
  classical
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
  · simp
  · intro j hj
    have h := (Twist.mem_negSupp n).mp hj
    split_ifs at h <;> omega

/-- The original coordinate indices identify exactly the degree-one monomials. -/
def paired_twist_linearCoordinateEquiv (n : ℕ) : Fin (n + 1) ≃ Twist.Mon n 1 ∅ :=
  Equiv.ofBijective (paired_twist_coordinateMonomial n) (by
    constructor
    · intro i j h
      have he := congrArg (fun a : Twist.Mon n 1 ∅ => a.val i) h
      change (if i = i then (1 : ℤ) else 0) = (if i = j then 1 else 0) at he
      simp only [ite_true] at he
      split_ifs at he with hij
      · exact hij
      · contradiction
    · intro a
      obtain ⟨i, hi, hz⟩ := paired_twist_linear_monomial a
      refine ⟨i, Subtype.ext (funext fun j => ?_)⟩
      change (if j = i then (1 : ℤ) else 0) = a.val j
      split_ifs with h
      · subst j; exact hi.symm
      · exact (hz j h).symm)

end HodgeLean.Foundations.Program.G32Native
