import HodgeLean.Foundations.TubularEuler.IndependentCovectorSurjectivityHelpers

/-! # Evaluating independent conormal covectors on ambient vectors

The output retains the original covector family and the original dual fibre.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

/-- Every functional on an injective family of conormal covectors is realized
by an ambient vector. No alternative normal fibre is introduced.
Source: Mathlib, `LinearMap.flip_surjective_iff₂`, and
`ContinuousLinearMap.coeLM`.
HC no distance; AV milestone no distance. -/
theorem injective_covector_evaluation_surjective
    {K C E : Type*} [NontriviallyNormedField K]
    [AddCommGroup C] [Module K C]
    [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
    (D : C →ₗ[K] (E →L[K] K)) (hD : Function.Injective D)
    (n : Module.Dual K C) :
    ∃ v : E, ∀ a : C, D a v = n a := by
  let B : C →ₗ[K] Module.Dual K E := (ContinuousLinearMap.coeLM K).comp D
  have hB : Function.Injective B := by
    intro a b hab
    apply hD
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hab v
  have hs : Function.Surjective B.flip := B.flip_surjective_iff₂.mpr hB
  obtain ⟨v, hv⟩ := hs n
  exact ⟨v, fun a => LinearMap.congr_fun hv a⟩

#print axioms injective_covector_evaluation_surjective

end HodgeLean.Foundations.TubularEuler
