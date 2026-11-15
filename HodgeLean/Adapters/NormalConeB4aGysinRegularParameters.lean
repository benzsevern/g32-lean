import HodgeLean.Adapters.NormalConeB4aGysinCriticalValues

noncomputable section
namespace HodgeLean.Adapters

/-- One arbitrarily small parameter is regular for every chart in a countable family
and avoids an additional prescribed null set. -/
theorem a3b4a_gysin_small_common_regular_parameter
    {n : ℕ} {ι : Type*} [Countable ι]
    (U : ι → Set (Fin n → ℂ)) (hU : ∀ j, IsOpen (U j))
    (f : ι → (Fin n → ℂ) → (Fin n → ℂ))
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j))
    (B : Set (Fin n → ℂ)) (hB : MeasureTheory.volume B = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Fin n → ℂ, ‖a‖ < ε ∧ a ∉ B ∧
      ∀ j x, x ∈ U j → f j x = a → IsUnit (fderiv ℂ (f j) x) := by
  classical
  let S : Option ι → Set (Fin n → ℂ)
    | none => B
    | some j => f j '' {x | x ∈ U j ∧ ¬ IsUnit (fderiv ℂ (f j) x)}
  have hS : ∀ j, MeasureTheory.volume (S j) = 0 := by
    intro j
    cases j with
    | none => exact hB
    | some j => exact a3b4a_gysin_complex_critical_values_null (U j) (hU j) (f j) (hf j)
  obtain ⟨a, ha, hav⟩ := a3b4a_gysin_small_parameter_avoiding_null_sets S hS ε hε
  refine ⟨a, ha, hav none, ?_⟩
  intro j x hx hfx
  by_contra hcrit
  exact hav (some j) ⟨x, ⟨hx, hcrit⟩, hfx⟩

end HodgeLean.Adapters
