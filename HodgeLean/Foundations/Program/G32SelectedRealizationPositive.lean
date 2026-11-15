import HodgeLean.Foundations.Program.G32SelectedRealizationSupplierHodge

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_coordinate_rank_positive {U F : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup F] [Module ℚ F] (V : Submodule ℚ U) (hV : V ≠ ⊥)
    {d : ℕ} (e : V ≃ₗ[ℚ] (Fin d → F)) : 0 < d := by
  by_contra h
  have hd : d = 0 := by omega
  subst d
  apply hV
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hh : e ⟨x, hx⟩ = e 0 := Subsingleton.elim _ _
  have hz := e.injective hh
  exact congrArg Subtype.val hz

end HodgeLean.Foundations.Program
