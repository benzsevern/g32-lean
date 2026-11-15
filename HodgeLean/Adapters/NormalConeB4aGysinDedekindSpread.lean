import HodgeLean.Adapters.NormalConeB4aGysinSpreadFlat

/-! # Flat neighborhoods over an affine Dedekind parameter base -/

noncomputable section
namespace HodgeLean.Adapters
open scoped nonZeroDivisors

/-- Flatness at one source stalk gives one denominator annihilating all
base torsion, simultaneously for every nonzero base element. -/
theorem a3b4a_gysin_exists_base_torsion_annihilator
    {D R : Type*} [CommRing D] [IsDomain D] [CommRing R] [IsNoetherianRing R]
    [Algebra D R] (p : Ideal R) [p.IsPrime]
    [Module.Flat D (Localization.AtPrime p)] :
    ∃ f : R, f ∉ p ∧ ∀ d : D, d ≠ 0 → ∀ r : R, d • r = 0 → f * r = 0 := by
  let N := Submodule.torsion' R R D⁰
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R N := by
    apply Module.notMem_support_iff'.mpr
    intro r
    obtain ⟨d, hd⟩ := r.property
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
      (R := D) (M := Localization.AtPrime p) (r := (d : D)) d.property
    have hz : algebraMap R (Localization.AtPrime p) (r : R) = 0 := by
      apply hreg
      change (d : D) • (r : R) = 0 at hd
      simpa only [Algebra.smul_def, IsScalarTower.algebraMap_apply D R
        (Localization.AtPrime p), map_mul, map_zero, mul_zero] using
        congrArg (algebraMap R (Localization.AtPrime p)) hd
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl
      (Localization.AtPrime p) (r : R)).mp hz
    exact ⟨s, s.property, Subtype.ext hs⟩
  have hnle : ¬ Module.annihilator R N ≤ p :=
    fun h => hnot (Module.mem_support_iff_of_finite.mpr h)
  obtain ⟨f, hf, hfp⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  refine ⟨f, hfp, ?_⟩
  intro d hd r hr
  let z : N := ⟨r, ⟨⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩, hr⟩⟩
  exact congrArg Subtype.val (Module.mem_annihilator.mp hf z)

/-- Flatness at a source stalk over a Dedekind domain spreads to a principal
source neighborhood without localizing the parameter base. -/
theorem a3b4a_gysin_exists_dedekind_flat_neighborhood
    {D R : Type*} [CommRing D] [IsDomain D] [IsDedekindDomain D]
    [CommRing R] [IsNoetherianRing R] [Algebra D R]
    (p : Ideal R) [p.IsPrime] [Module.Flat D (Localization.AtPrime p)] :
    ∃ f : R, f ∉ p ∧ Module.Flat D (Localization.Away f) := by
  obtain ⟨f, hf, hann⟩ := a3b4a_gysin_exists_base_torsion_annihilator (D := D) p
  refine ⟨f, hf, ?_⟩
  have : Module.IsTorsionFree D (Localization.Away f) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun d z hz => by
      by_cases hd : d = 0
      · exact Or.inl hd
      · right
        have hreg := a3b4a_gysin_regular_away_of_torsion_annihilator
          (algebraMap D R d) f (fun r hr => hann d hd r (by simpa only [Algebra.smul_def] using hr))
        have hregD : IsSMulRegular (Localization.Away f) d := by
          simpa only [IsSMulRegular, Algebra.smul_def, Algebra.algebraMap_self_apply,
            ← IsScalarTower.algebraMap_apply D R (Localization.Away f)] using hreg
        exact hregD (hz.trans (smul_zero d).symm))
  infer_instance

end HodgeLean.Adapters
