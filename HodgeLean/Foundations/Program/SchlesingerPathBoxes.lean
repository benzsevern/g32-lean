import HodgeLean.Foundations.Program.SchlesingerPathDefs

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65p_boxCentre_separated : ∀ k l : Fin 12, k ≠ l →
    (1 / 5000 : ℝ) ≤ |((b65b_boxCentre k).1 : ℝ) - ((b65b_boxCentre l).1 : ℝ)| ∨
    (1 / 5000 : ℝ) ≤ |((b65b_boxCentre k).2 : ℝ) - ((b65b_boxCentre l).2 : ℝ)| := by
  intro k l
  fin_cases k <;> fin_cases l <;> norm_num [b65b_boxCentre]

theorem b65p_boxes_injective (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ)) :
    Function.Injective p := by
  have hidx : Function.Surjective b65b_boxIndex := by decide
  intro a b hab
  obtain ⟨k, rfl⟩ := hidx a
  obtain ⟨l, rfl⟩ := hidx b
  have hkl : k = l := by
    by_contra hne
    have hre := congrArg Complex.re hab
    have him := congrArg Complex.im hab
    have hkre := (abs_lt.mp (hp k).1)
    have hlre := (abs_lt.mp (hp l).1)
    have hkim := (abs_lt.mp (hp k).2)
    have hlim := (abs_lt.mp (hp l).2)
    rcases b65p_boxCentre_separated k l hne with h | h
    · have h' : (1 / 5000 : ℝ) ≤
          |((b65b_boxCentre k).1 : ℝ) - ((b65b_boxCentre l).1 : ℝ)| := h
      rcases le_or_gt ((b65b_boxCentre k).1 : ℝ) ((b65b_boxCentre l).1 : ℝ) with hle | hgt
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h'; linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)] at h'; linarith
    · have h' : (1 / 5000 : ℝ) ≤
          |((b65b_boxCentre k).2 : ℝ) - ((b65b_boxCentre l).2 : ℝ)| := h
      rcases le_or_gt ((b65b_boxCentre k).2 : ℝ) ((b65b_boxCentre l).2 : ℝ) with hle | hgt
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h'; linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)] at h'; linarith
  exact congrArg b65b_boxIndex hkl

end HodgeLean.Foundations.Program
