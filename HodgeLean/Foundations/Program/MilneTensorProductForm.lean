import HodgeLean.Foundations.Program.MilneTensorComplement

noncomputable section
namespace HodgeLean.Foundations.Program
variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

theorem m1b_prodBilin_nondegenerate
    (A : LinearMap.BilinForm ℂ U) (B : LinearMap.BilinForm ℂ W)
    (hA : A.Nondegenerate) (hB : B.Nondegenerate) :
    (m1b_prodBilin A B).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hA.1
      intro y
      have h := hx (y, 0)
      change A x.1 y + B x.2 0 = 0 at h
      simpa only [map_zero, add_zero] using h
    · apply hB.1
      intro y
      have h := hx (0, y)
      change A x.1 0 + B x.2 y = 0 at h
      simpa only [map_zero, zero_add] using h
  · intro y hy
    apply Prod.ext
    · apply hA.2
      intro x
      have h := hy (x, 0)
      change A x y.1 + B 0 y.2 = 0 at h
      simpa only [map_zero, LinearMap.zero_apply, add_zero] using h
    · apply hB.2
      intro x
      have h := hy (0, x)
      change A 0 y.1 + B x y.2 = 0 at h
      simpa only [map_zero, LinearMap.zero_apply, zero_add] using h

end HodgeLean.Foundations.Program
