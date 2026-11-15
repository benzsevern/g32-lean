import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.IsBaseChange

/-! Torsion detected by scalar extension over a Dedekind domain.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace HodgeLean.Foundations.IntegralHomology

theorem baseChange_zero_mem_torsion
    {R S M N : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [CommRing S] [Algebra R S] [FaithfulSMul R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) (hf : IsBaseChange S f)
    (m : M) (hm : f m = 0) : m ∈ Submodule.torsion R M := by
  have ht : (1 : S) ⊗ₜ[R] m = 0 := by
    apply hf.equiv.injective
    rw [hf.equiv_tmul, hm, smul_zero, map_zero]
  let q := (Submodule.torsion R M).mkQ
  have hq : (1 : S) ⊗ₜ[R] q m = 0 := by
    have h := congrArg (q.baseChange S) ht
    simpa only [LinearMap.baseChange_tmul, map_zero] using h
  have hmQ : q m = 0 := by
    apply Module.Flat.tensorProduct_mk_injective (R := R) (S := S)
      (M := M ⧸ Submodule.torsion R M)
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using hq
  exact (Submodule.Quotient.mk_eq_zero _).mp hmQ

theorem torsion_le_ker_field {R S M N : Type} [CommRing R] [IsDomain R]
    [Field S] [Algebra R S] [FaithfulSMul R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) :
    Submodule.torsion R M ≤ LinearMap.ker f := by
  intro a ha
  obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff a).mp ha
  have hr' : (r : R) • a = 0 := hr
  have hz : (algebraMap R S (r : R)) • f a = 0 := by
    rw [IsScalarTower.algebraMap_smul, ← map_smul, hr', map_zero]
  exact (smul_eq_zero.mp hz).resolve_left
    (by simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective R S).ne (nonZeroDivisors.coe_ne_zero r))

end HodgeLean.Foundations.IntegralHomology
