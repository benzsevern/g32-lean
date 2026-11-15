import HodgeLean.Foundations.Program.SchoenTowerL1bKummerRoots

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Either signed exponential gives a primitive character of the specified order. -/
theorem s2v_l1b_signed_character_primitive (m : ℕ) (hm : m ≠ 0)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    IsPrimitiveRoot (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ))) m := by
  rcases hs with rfl | rfl
  · simpa only [Int.cast_one, one_mul] using Complex.isPrimitiveRoot_exp m hm
  · have hh := (Complex.isPrimitiveRoot_exp m hm).inv
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_div,
      Complex.exp_neg] using hh

end HodgeLean.Foundations.Program
