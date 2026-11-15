import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralBaseChange

/-! The kernel of coefficient extension consists of torsion classes. -/
noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem s4_c1a6_baseChange_zero_mem_torsion
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

theorem s4_c1a6_zToCHomology_zero_mem_torsion (X : TopCat) (n : ℕ)
    (a : (s4_c1a6_zbc_ZChains X).homology n)
    (ha : s4_c1a6_zbc_zToCHomology X n a = 0) :
    a ∈ Submodule.torsion ℤ ((s4_c1a6_zbc_ZChains X).homology n) :=
  s4_c1a6_baseChange_zero_mem_torsion _
    (s4_c1a6_zbc_zToCHomology_isBaseChange X n) a ha

end HodgeLean.Foundations.Program
