import HodgeLean.Adapters.NormalConeB4aGysinSpreadParameters
import Mathlib.RingTheory.Support

/-! # Principal neighborhoods where a stalkwise regular parameter stays regular -/

noncomputable section
namespace HodgeLean.Adapters

/-- Stalkwise injectivity of a parameter gives one denominator outside the
prime annihilating every element killed by that parameter. -/
theorem a3b4a_gysin_exists_uniform_torsion_annihilator
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (t : R)
    (hreg : IsSMulRegular (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) t)) :
    ∃ f : R, f ∉ p ∧ ∀ r : R, t * r = 0 → f * r = 0 := by
  let N := LinearMap.ker (LinearMap.mulLeft R t)
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R N := by
    apply Module.notMem_support_iff'.mpr
    intro r
    have hr : t * (r : R) = 0 := r.property
    have hz : algebraMap R (Localization.AtPrime p) (r : R) = 0 := by
      apply hreg
      change algebraMap R (Localization.AtPrime p) t *
        algebraMap R (Localization.AtPrime p) (r : R) =
        algebraMap R (Localization.AtPrime p) t * 0
      rw [← map_mul, hr, map_zero, mul_zero]
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl
      (Localization.AtPrime p) (r : R)).mp hz
    refine ⟨s, s.property, ?_⟩
    exact Subtype.ext hs
  have hnle : ¬ Module.annihilator R N ≤ p :=
    fun h => hnot (Module.mem_support_iff_of_finite.mpr h)
  obtain ⟨f, hf, hfp⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  refine ⟨f, hfp, ?_⟩
  intro r hr
  exact congrArg Subtype.val (Module.mem_annihilator.mp hf (⟨r, hr⟩ : N))

/-- Inverting an annihilator of parameter torsion makes the parameter
injective on the localized ring. -/
theorem a3b4a_gysin_regular_away_of_torsion_annihilator
    {R : Type*} [CommRing R] (t f : R)
    (hann : ∀ r : R, t * r = 0 → f * r = 0) :
    IsSMulRegular (Localization.Away f) (algebraMap R (Localization.Away f) t) := by
  let L := Localization.Away f
  have hzero : ∀ z : L, algebraMap R L t * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) z
    have htr : algebraMap R L (t * r) = 0 := by
      rw [map_mul, ← hs, ← mul_assoc, hz, zero_mul]
    obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) L (t * r)).mp htr
    have hkill : f * ((u : R) * r) = 0 :=
      hann ((u : R) * r) (by simpa only [mul_left_comm] using hu)
    have hunit : IsUnit (algebraMap R L (f * (u : R))) := by
      rw [map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit f).mul (IsLocalization.map_units L u)
    have hr : algebraMap R L r = 0 := hunit.mul_right_eq_zero.mp (by
      rw [← map_mul, mul_assoc, hkill, map_zero])
    exact (IsLocalization.map_units L s).mul_left_eq_zero.mp (hs.trans hr)
  intro a b hab
  apply sub_eq_zero.mp
  apply hzero
  change algebraMap R L t * a = algebraMap R L t * b at hab
  rw [mul_sub, hab, sub_self]

/-- Flatness over a DVR at a source stalk spreads to a principal source
neighborhood, with no module-finiteness assumption over the DVR. -/
theorem a3b4a_gysin_exists_flat_principal_neighborhood
    {D R : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing R] [IsNoetherianRing R] [Algebra D R]
    (π : D) (hπ : Irreducible π) (p : Ideal R) [p.IsPrime]
    [Module.Flat D (Localization.AtPrime p)] :
    ∃ f : R, f ∉ p ∧ Module.Flat D (Localization.Away f) := by
  let L := Localization.AtPrime p
  have hπreg : IsSMulRegular L π := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := L) (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero)
  have hreg : IsSMulRegular L (algebraMap R L (algebraMap D R π)) := by
    simpa only [IsSMulRegular, Algebra.smul_def, Algebra.algebraMap_self_apply,
      ← IsScalarTower.algebraMap_apply D R L] using hπreg
  obtain ⟨f, hfp, hann⟩ :=
    a3b4a_gysin_exists_uniform_torsion_annihilator p (algebraMap D R π) hreg
  refine ⟨f, hfp, ?_⟩
  apply a3b4a_gysin_flat_of_uniformizer_regular π hπ
  have h := a3b4a_gysin_regular_away_of_torsion_annihilator (algebraMap D R π) f hann
  simpa only [IsSMulRegular, Algebra.smul_def, Algebra.algebraMap_self_apply,
    ← IsScalarTower.algebraMap_apply D R (Localization.Away f)] using h

end HodgeLean.Adapters
