import HodgeLean.Foundations.Program.PrymVariationCentreFormula

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b63d_rep_age_conjugate {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) (g h : G) :
    b4_age (ρ (g * h * g⁻¹)) = b4_age (ρ h) := by
  let e : W ≃ₗ[ℂ] W :=
    { toLinearMap := ρ g
      invFun := ρ g⁻¹
      left_inv := fun v ↦ by
        change (ρ g⁻¹ * ρ g) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun v ↦ by
        change (ρ g * ρ g⁻¹) v = v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  have he : e.conj (ρ h) = ρ (g * h * g⁻¹) := by
    apply LinearMap.ext
    intro v
    change ρ g (ρ h (ρ g⁻¹ v)) = ρ (g * h * g⁻¹) v
    rw [map_mul, map_mul]
    rfl
  simp only [b4_age, ← he, LinearEquiv.charpoly_conj]

theorem b63d_rep_rank_conjugate {G W : Type} [Group G] [Finite G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) (g h : G) :
    Module.finrank ℂ (LinearMap.range (ρ (g * h * g⁻¹) - LinearMap.id)) =
      Module.finrank ℂ (LinearMap.range (ρ h - LinearMap.id)) := by
  have h1 := HurwitzPrymRex_age_add_bar ρ (g * h * g⁻¹)
  have h2 := HurwitzPrymRex_age_add_bar ρ h
  rw [b63d_rep_age_conjugate, b63d_rep_age_conjugate] at h1
  exact_mod_cast h1.symm.trans h2

end HodgeLean.Foundations.Program
