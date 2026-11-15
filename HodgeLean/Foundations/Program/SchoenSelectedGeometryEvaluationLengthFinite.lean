import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationLength

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Local evaluation fibres of finite complex algebras have finite length.
Source: the Artinian finite fibre and its localized parameter-length identification. -/
theorem s0_evaluation_length_finite
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (u : B →ₐ[ℂ] ℂ) (w : T →ₐ[ℂ] ℂ)
    (hw : w.comp (IsScalarTower.toAlgHom ℂ B T) = u) :
    ∃ m : ℕ, a3b4a_gysin_evaluationSliceLength u w = m := by
  let p := RingHom.ker u
  letI : p.IsPrime := RingHom.ker_isPrime u
  letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  obtain ⟨E, hE⟩ := a3b4a_gysin_fibre_evaluation_equiv (T := T) p u rfl
  let Q := E ⟨w, hw⟩
  have hlen := a3b4a_gysin_fibre_prime_parameter_length p Q.asIdeal
  have htransport (r : Ideal T) [r.IsPrime] (hr : r = RingHom.ker w) :
      Module.length (Localization.AtPrime r)
        (Localization.AtPrime r ⧸ p.map (algebraMap B (Localization.AtPrime r))) =
        a3b4a_gysin_evaluationSliceLength u w := by
    subst r
    rfl
  have heq := hlen.trans (htransport _ (hE ⟨w, hw⟩))
  letI : IsArtinianRing (p.Fiber T) :=
    isArtinian_of_tower p.ResidueField (inferInstance : IsArtinian p.ResidueField (p.Fiber T))
  have hfinite : Module.length (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q.asIdeal) ≠ ⊤ := Module.length_ne_top_iff.mpr
        (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  rw [heq] at hfinite
  exact ⟨(a3b4a_gysin_evaluationSliceLength u w).toNat, (ENat.natCast_toNat hfinite).symm⟩

#print axioms s0_evaluation_length_finite
end HodgeLean.Foundations.Program
