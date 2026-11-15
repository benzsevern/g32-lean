import HodgeLean.Adapters.NormalConeB4aGysinFibreEvaluationSum

noncomputable section
namespace HodgeLean.Adapters

/-- Every fibre of the complex evaluation map of a finite algebra is finite. -/
theorem a3b4a_gysin_finite_evaluation_fibre
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (u : B →ₐ[ℂ] ℂ) :
    Set.Finite {w : T →ₐ[ℂ] ℂ | w.comp (IsScalarTower.toAlgHom ℂ B T) = u} := by
  classical
  let p := RingHom.ker u
  letI : p.IsPrime := RingHom.ker_isPrime u
  obtain ⟨E, _⟩ := a3b4a_gysin_fibre_evaluation_equiv (T := T) p u rfl
  letI : IsArtinianRing (p.Fiber T) :=
    isArtinian_of_tower p.ResidueField (inferInstance : IsArtinian p.ResidueField (p.Fiber T))
  exact Set.finite_coe_iff.mp (Finite.of_equiv (PrimeSpectrum (p.Fiber T)) E.symm)

end HodgeLean.Adapters
