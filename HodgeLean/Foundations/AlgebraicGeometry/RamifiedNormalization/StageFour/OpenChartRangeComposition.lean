import Mathlib.Data.Set.Function

set_option Elab.async false
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Exact chart images pass through an injective open-model comparison square. -/
theorem open_chart_range_composition
    {A B X Y X' Y' : Type*}
    (i : A → X') (j : B → Y') (J : X' → X) (u : Y' → Y)
    (p : X → Y) (p' : X' → Y')
    (hu : Function.Injective u) (hsquare : ∀ x, p (J x) = u (p' x))
    (hJ : Set.range J = p ⁻¹' Set.range u)
    (hi : Set.range i = p' ⁻¹' Set.range j) :
    Set.range (J ∘ i) = p ⁻¹' Set.range (u ∘ j) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have ha : i a ∈ Set.range i := Set.mem_range_self a
    rw [hi] at ha
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, (congrArg u hb).trans (hsquare (i a)).symm⟩
  · rintro ⟨b, hb⟩
    have hx : x ∈ Set.range J := by
      rw [hJ]
      exact ⟨j b, hb⟩
    obtain ⟨z, rfl⟩ := hx
    have hz : p' z ∈ Set.range j := ⟨b, hu (hb.trans (hsquare z))⟩
    have hz' : z ∈ Set.range i := by
      rw [hi]
      exact hz
    obtain ⟨a, ha⟩ := hz'
    exact ⟨a, congrArg J ha⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
