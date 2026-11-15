import HodgeLean.Foundations.Program.PrymParabolicIntersectionOrientation

noncomputable section
namespace HodgeLean.Foundations.Program

theorem hga_triangle_dual_orientation (a b c : ℂ) :
    b3_orient ℂ (b - a) ((a + b + c) / 3 - (a + b) / 2) =
      b3_orient ℂ (b - a) (c - a) / 3 := by
  conv_lhs => rw [hga_b3_orient_complex]
  conv_rhs => rw [hga_b3_orient_complex]
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
    Complex.add_re, Complex.add_im]
  norm_num [Complex.normSq]
  ring

theorem hga_triangle_dual_crossing (a b c : ℂ)
    (h : b3_orient ℂ (b - a) (c - a) ≠ 0) (s t : ℝ)
    (he : a + (s : ℂ) * (b - a) =
      (a + b) / 2 + (t : ℂ) * ((a + b + c) / 3 - (a + b) / 2)) :
    s = 1 / 2 ∧ t = 0 := by
  have hd : b3_orient ℂ (b - a) ((a + b + c) / 3 - (a + b) / 2) ≠ 0 := by
    rw [hga_triangle_dual_orientation]
    exact div_ne_zero h (by norm_num)
  have hz : (s - 1 / 2) • (b - a) + (-t) • ((a + b + c) / 3 - (a + b) / 2) = 0 := by
    simp only [← Complex.coe_smul, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg]
    linear_combination he
  obtain ⟨hs, ht⟩ := b3A_indep_of_orient _ _ hd _ _ hz
  exact ⟨sub_eq_zero.mp hs, neg_eq_zero.mp ht⟩

theorem hga_triangle_dual_crossing_positive (a b c : ℂ)
    (h : b3_orient ℂ (b - a) (c - a) < 0) :
    0 < b3_orient ℂ ((a + b + c) / 3 - (a + b) / 2) (b - a) := by
  rw [b3A_orient_swap, hga_triangle_dual_orientation]
  exact neg_pos.mpr (div_neg_of_neg_of_pos h (by norm_num))

#print axioms hga_triangle_dual_crossing_positive
#print axioms hga_triangle_dual_crossing
#print axioms hga_triangle_dual_orientation
end HodgeLean.Foundations.Program
