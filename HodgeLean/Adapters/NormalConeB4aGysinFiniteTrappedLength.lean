import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationLength
import HodgeLean.Adapters.NormalConeB4aGysinFiniteModelTrapping

noncomputable section
namespace HodgeLean.Adapters

/-- Prescribing any open neighborhood of the marked local fibre only
shrinks the base neighborhood for its exact length conservation. -/
theorem a3b4a_gysin_finite_evaluation_length_trapping
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Algebra.FiniteType ℂ B]
    [Module.FinitePresentation B T] [Module.Flat B T]
    (p : Ideal B) [p.IsPrime] (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    [IsLocalRing (p.Fiber T)] (w₀ : T →ₐ[ℂ] ℂ)
    (hw₀ : w₀.comp (IsScalarTower.toAlgHom ℂ B T) = u)
    (N : Set (T →ₐ[ℂ] ℂ)) (hN : IsOpen N) (hwN : w₀ ∈ N) :
    ∃ V : Set (B →ₐ[ℂ] ℂ), IsOpen V ∧ u ∈ V ∧
      ∀ v ∈ V, ∃ F : Finset (T →ₐ[ℂ] ℂ),
        (∀ w, w ∈ F ↔ w ∈ N ∧ w.comp (IsScalarTower.toAlgHom ℂ B T) = v) ∧
        ∑ w ∈ F, a3b4a_gysin_evaluationSliceLength v w =
          Module.length (p.Fiber T) (p.Fiber T) := by
  obtain ⟨V₀, hV₀, hu₀, hlength⟩ :=
    a3b4a_gysin_finite_evaluation_length_neighborhood (T := T) p u hu
  obtain ⟨V₁, hV₁, hu₁, htrap⟩ :=
    a3b4a_gysin_finite_local_fibre_trapping p u hu w₀ hw₀ N hN hwN
  refine ⟨V₀ ∩ V₁, hV₀.inter hV₁, ⟨hu₀, hu₁⟩, ?_⟩
  intro v hv
  obtain ⟨F, hF, hsum⟩ := hlength v hv.1
  refine ⟨F, ?_, hsum⟩
  intro w
  constructor
  · intro hw
    have hres := (hF w).mp hw
    refine ⟨htrap w ?_, hres⟩
    rw [hres]
    exact hv.2
  · intro hw
    exact (hF w).mpr hw.2

end HodgeLean.Adapters
