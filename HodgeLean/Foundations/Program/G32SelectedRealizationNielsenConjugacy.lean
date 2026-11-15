import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_nielsen_group_conjugacy (g : Fin 13 → g32p_G)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j))) :
    ∃ σ : Equiv.Perm (Fin 13), ∀ j, ∃ k : g32p_G,
      g j = k * g32p_classDatum (σ j) * k⁻¹ := by
  obtain ⟨σ, hs⟩ := hg.1
  refine ⟨σ, fun j ↦ ?_⟩
  obtain ⟨a, ha, b, hb, hab, he⟩ := hs j
  let k : g32p_G := ⟨a, ha⟩
  let l : g32p_G := ⟨b, hb⟩
  have hkl : k * l = 1 := Subtype.ext hab
  have hl : l = k⁻¹ := by
    calc
      l = k⁻¹ * (k * l) := by simp
      _ = k⁻¹ := by rw [hkl, mul_one]
  refine ⟨k, ?_⟩
  calc
    g j = k * g32p_classDatum (σ j) * l := Subtype.ext he
    _ = _ := by rw [hl]

end HodgeLean.Foundations.Program
