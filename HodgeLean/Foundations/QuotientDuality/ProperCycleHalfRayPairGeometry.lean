import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexRelativeNaturality

/-! # Literal supports in the real half-ray relative sequence
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The intersection of the two actual half-ray complements is the entire axis complement. -/
theorem properCycle_half_ray_complement_intersection (Y : Type) (y : Y) :
    ({z : ℝ × Y | 0 ≤ z.1 ∧ z.2 = y}ᶜ ∩ {z : ℝ × Y | z.1 ≤ 0 ∧ z.2 = y}ᶜ) =
      {z : ℝ × Y | z.2 ≠ y} := by
  ext z
  constructor
  · rintro ⟨hp,hq⟩ he
    by_cases hx : 0 ≤ z.1
    · exact hp ⟨hx,he⟩
    · exact hq ⟨le_of_not_ge hx,he⟩
  · intro hz
    exact ⟨fun h => hz h.2, fun h => hz h.2⟩

/-- The union of the two actual half-ray complements is the original point complement. -/
theorem properCycle_half_ray_complement_union (Y : Type) (y : Y) :
    ({z : ℝ × Y | 0 ≤ z.1 ∧ z.2 = y}ᶜ ∪ {z : ℝ × Y | z.1 ≤ 0 ∧ z.2 = y}ᶜ) =
      ({(0,y)}ᶜ : Set (ℝ × Y)) := by
  ext z
  constructor
  · rintro (hp | hq) he
    · subst z; exact hp ⟨le_rfl,rfl⟩
    · subst z; exact hq ⟨le_rfl,rfl⟩
  · intro hz
    by_cases hp : 0 ≤ z.1 ∧ z.2 = y
    · right
      intro hq
      exact hz (Prod.ext (le_antisymm hq.1 hp.1) hp.2)
    · exact Or.inl hp

end HodgeLean.Foundations.QuotientDuality
