import HodgeLean.Foundations.Program.MilneTensorPairedSchur

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_pairForm_alternating (x : Fin 2 → ℂ) : m1b_pairForm x x = 0 := by
  change x 0 * x 1 - x 1 * x 0 = 0
  ring

theorem m1b_pairForm_nondegenerate : m1b_pairForm.Nondegenerate := by
  constructor
  · intro x hx
    funext i
    fin_cases i
    · have h := hx (Pi.single 1 1)
      change x 0 * 1 - x 1 * 0 = 0 at h
      simpa using h
    · have h := hx (Pi.single 0 1)
      change x 0 * 0 - x 1 * 1 = 0 at h
      simpa using h
  · intro y hy
    funext i
    fin_cases i
    · have h := hy (Pi.single 1 1)
      change 0 * y 1 - 1 * y 0 = 0 at h
      simpa using h
    · have h := hy (Pi.single 0 1)
      change 1 * y 1 - 0 * y 0 = 0 at h
      simpa using h

end HodgeLean.Foundations.Program
