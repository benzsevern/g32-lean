import HodgeLean.Foundations.Program.MilneTensorDefs

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem m1b_adjoint_norm_one_set (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (τ : Module.End ℂ V → Module.End ℂ V)
    (hadj : ∀ u x y, B (u x) y = B x (τ u y)) :
    {u | τ u * u = 1} = m1b_isometries B := by
  ext u
  constructor
  · intro hu
    refine ⟨isUnit_iff_exists_inv'.mpr ⟨τ u, hu⟩, ?_⟩
    intro x y
    rw [hadj]
    have hy := LinearMap.congr_fun hu y
    change τ u (u y) = y at hy
    rw [hy]
  · rintro ⟨_, hu⟩
    ext y
    apply sub_eq_zero.mp
    apply hB.2
    intro x
    rw [map_sub]
    apply sub_eq_zero.mpr
    change B x (τ u (u y)) = B x y
    rw [← hadj, hu]

end HodgeLean.Foundations.Program
