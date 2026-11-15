import HodgeLean.Adapters.NormalConeB4aGysinFinitePointTrapping

noncomputable section
namespace HodgeLean.Adapters

/-- Near a local special fibre, all points of nearby finite-model fibres
lie in any prescribed open neighborhood of its marked evaluation. -/
theorem a3b4a_gysin_finite_local_fibre_trapping
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Algebra.FiniteType ℂ B] [Module.Finite B T]
    (p : Ideal B) [p.IsPrime] [IsLocalRing (p.Fiber T)]
    (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    (w₀ : T →ₐ[ℂ] ℂ) (hw₀ : w₀.comp (IsScalarTower.toAlgHom ℂ B T) = u)
    (N : Set (T →ₐ[ℂ] ℂ)) (hN : IsOpen N) (hwN : w₀ ∈ N) :
    ∃ V : Set (B →ₐ[ℂ] ℂ), IsOpen V ∧ u ∈ V ∧
      ∀ w : T →ₐ[ℂ] ℂ, w.comp (IsScalarTower.toAlgHom ℂ B T) ∈ V → w ∈ N := by
  let π := fun w : T →ₐ[ℂ] ℂ => w.comp (IsScalarTower.toAlgHom ℂ B T)
  have hproper : IsProperMap π := a3b4a_gysin_finite_evaluation_isProperMap
  refine ⟨(π '' Nᶜ)ᶜ, (hproper.isClosedMap Nᶜ hN.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨w, hw, heval⟩
    have heq := a3b4a_gysin_finite_local_fibre_evaluation_unique p u hu w w₀ heval hw₀
    exact hw (heq.symm ▸ hwN)
  · intro w hw
    by_contra hn
    exact hw ⟨w, hn, rfl⟩

end HodgeLean.Adapters
