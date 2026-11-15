import HodgeLean.Foundations.Program.G32SelectedRealizationHolomorphicMultiplicity

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_linear_character_invariants {G : Type*} [Group G]
    (χ : G →* ℂˣ) (hχ : ∃ g, χ g ≠ 1) :
    Representation.invariants (papersLinRep χ).ρ = ⊥ := by
  let ρ : Representation ℂ G ℂ := (papersLinRep χ).ρ
  change Representation.invariants ρ = ⊥
  obtain ⟨g, hg⟩ := hχ
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hh := (Representation.mem_invariants _ x).mp hx g
  change (χ g : ℂ) * x = x at hh
  have he : ((χ g : ℂ) - 1) * x = 0 := by linear_combination hh
  apply (mul_eq_zero.mp he).resolve_left
  exact sub_ne_zero.mpr (fun h ↦ hg (Units.ext h))

end HodgeLean.Foundations.Program
