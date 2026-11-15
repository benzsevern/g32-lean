import HodgeLean.Adapters.NormalConeB4aGysinRegularSlice
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Flatness of regular slices over a discrete valuation ring -/

noncomputable section
namespace HodgeLean.Adapters

/-- Injectivity of a uniformizer on a module over a discrete valuation ring
implies flatness, without any module-finiteness hypothesis. -/
theorem a3b4a_gysin_flat_of_uniformizer_regular
    {A M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [AddCommGroup M] [Module A M] (π : A) (hπ : Irreducible π)
    (hreg : IsSMulRegular M π) : Module.Flat A M := by
  have : Module.IsTorsionFree A M := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha.ne_zero hπ
    exact (u.isUnit.isSMulRegular (M := M)).mul (hreg.pow n)
  infer_instance

/-- A regular sequence on the special fibre of a flat local algebra over a DVR
cuts out another flat algebra over that DVR. -/
theorem a3b4a_gysin_regular_slice_flat
    {A R : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
    [Module.Flat A R] (π : A) (hπ : Irreducible π) (xs : List R)
    (hxs : RingTheory.Sequence.IsRegular (QuotSMulTop (algebraMap A R π) R) xs) :
    Module.Flat A (R ⧸ Ideal.ofList xs) := by
  have ht : IsSMulRegular R (algebraMap A R π) := by
    simpa only [IsSMulRegular, Algebra.smul_def, Algebra.algebraMap_self_apply] using
      (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R)
        (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero))
  have h := a3b4a_gysin_parameter_regular_after_slice (algebraMap A R π) xs ht hxs
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at h
  apply a3b4a_gysin_flat_of_uniformizer_regular π hπ
  intro a b hab
  apply h
  simpa only [IsScalarTower.algebraMap_smul] using hab

end HodgeLean.Adapters
