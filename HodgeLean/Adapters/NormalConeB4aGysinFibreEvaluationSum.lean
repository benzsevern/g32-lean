import HodgeLean.Adapters.NormalConeB4aGysinFibrePointLength

noncomputable section
namespace HodgeLean.Adapters

/-- Summing over complex evaluations retains every full local fibre length. -/
theorem a3b4a_gysin_fibre_evaluation_length_sum
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (p : Ideal B) [p.IsPrime] (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p) :
    (∑ᶠ w : {w : T →ₐ[ℂ] ℂ // w.comp (IsScalarTower.toAlgHom ℂ B T) = u},
      letI : (RingHom.ker w.val).IsPrime := RingHom.ker_isPrime w.val
      let L := Localization.AtPrime (RingHom.ker w.val)
      Module.length L (L ⧸ p.map (algebraMap B L))) =
      ∑ᶠ x : PrimeSpectrum (p.Fiber T),
        Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal) := by
  classical
  obtain ⟨E, hE⟩ := a3b4a_gysin_fibre_evaluation_equiv (T := T) p u hu
  rw [← finsum_comp_equiv E]
  apply finsum_congr
  intro w
  have h := a3b4a_gysin_fibre_prime_parameter_length p (E w).asIdeal
  letI : (RingHom.ker w.val).IsPrime := RingHom.ker_isPrime w.val
  have htransport (r : Ideal T) [r.IsPrime] (hr : r = RingHom.ker w.val) :
      Module.length (Localization.AtPrime r)
        (Localization.AtPrime r ⧸ p.map (algebraMap B (Localization.AtPrime r))) =
      Module.length (Localization.AtPrime (RingHom.ker w.val))
        (Localization.AtPrime (RingHom.ker w.val) ⧸
          p.map (algebraMap B (Localization.AtPrime (RingHom.ker w.val)))) := by
    subst r
    rfl
  exact (h.trans (htransport _ (hE w))).symm

end HodgeLean.Adapters
