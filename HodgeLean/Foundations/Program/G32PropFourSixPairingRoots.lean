import HodgeLean.Foundations.Program.G32PropFourSixPacked0003

namespace HodgeLean.Foundations.Program

theorem g32p_pairing_modulus_three {z : ℂ} (h : IsPrimitiveRoot z 3) :
    g32p_coeffEval z [1, 1, 1] = 0 := by
  have he := h.isRoot_cyclotomic (by decide : 0 < 3)
  rw [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] at he
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at he
  simp only [g32p_coeffEval, Int.cast_one, mul_zero, add_zero]
  linear_combination he

theorem g32p_pairing_modulus_six {z : ℂ} (h : IsPrimitiveRoot z 6) :
    g32p_coeffEval z [1, -1, 1] = 0 := by
  have he := h.isRoot_cyclotomic (by decide : 0 < 6)
  rw [Polynomial.cyclotomic_six, Polynomial.IsRoot.def] at he
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one] at he
  simp only [g32p_coeffEval, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
  linear_combination he

theorem g32p_pairing_modulus_twelve {z : ℂ} (h : IsPrimitiveRoot z 12) :
    g32p_coeffEval z [1, 0, -1, 0, 1] = 0 := by
  have hp : IsPrimitiveRoot (z ^ 2) 6 := h.pow_of_dvd (by decide) (by decide)
  have he := g32p_pairing_modulus_six hp
  simp only [g32p_coeffEval, Int.cast_one, Int.cast_zero, Int.cast_neg,
    mul_zero, add_zero, zero_add] at he ⊢
  linear_combination he

theorem g32p_pairing_modulus_fifteen {z : ℂ} (h : IsPrimitiveRoot z 15) :
    g32p_coeffEval z [1, -1, 0, 1, -1, 1, 0, -1, 1] = 0 := by
  have hp : IsPrimitiveRoot (z ^ 5) 3 := h.pow_of_dvd (by decide) (by decide)
  have he := g32p_pairing_modulus_three hp
  have hn : z ^ 2 + z + 1 ≠ 0 := by
    intro hz
    have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * hz
    have hd := (h.pow_eq_one_iff_dvd 3).mp hz3
    norm_num at hd
  apply (mul_eq_zero.mp (show
    g32p_coeffEval z [1, -1, 0, 1, -1, 1, 0, -1, 1] * (z ^ 2 + z + 1) = 0 from ?_)).resolve_right hn
  simp only [g32p_coeffEval, Int.cast_one, Int.cast_zero, Int.cast_neg,
    mul_zero, add_zero, zero_add] at he ⊢
  linear_combination he

end HodgeLean.Foundations.Program
