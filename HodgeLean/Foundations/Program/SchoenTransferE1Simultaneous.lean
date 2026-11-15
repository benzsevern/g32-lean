import HodgeLean.Foundations.CyclicAction
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-! Simultaneous character summands of commuting finite-order complex operators. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

open Polynomial
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace HodgeLean.Foundations.Program

/-- A finite-order complex operator is semisimple.
Source: Schoen (1988), Lemma 1.2, pp. 5–6; separability of X^m − 1 in characteristic zero. -/
theorem s4_e1_finite_order_semisimple
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) {m : ℕ} (hm : 0 < m) (hf : f ^ m = 1) :
    f.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (X ^ m - C 1 : ℂ[X]))
    (separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree
  simp only [map_sub, map_pow, aeval_X, aeval_C, hf, map_one, sub_self]

/-- Commuting finite-order operators have an internal simultaneous eigenspace decomposition.
Source: Schoen (1988), Lemma 1.2, pp. 5–6; simultaneous diagonalization. -/
theorem s4_e1_simultaneous_eigenspace_decomposition
    {ι V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : ι → Module.End ℂ V) {m : ℕ} (hm : 0 < m)
    (hf : ∀ i, f i ^ m = 1) (hcomm : ∀ i j, Commute (f i) (f j)) :
    DirectSum.IsInternal (fun c : ι → ℂ => ⨅ i, Module.End.eigenspace (f i) (c i)) := by
  classical
  have hs i := s4_e1_finite_order_semisimple (f i) hm (hf i)
  have hg i μ : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hs i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · have hi := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ)
    simpa only [hg] using hi
  · have ht := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j) (fun i => by
        simpa only [hg] using (hs i).iSup_eigenspace_eq_top)
    simpa only [hg] using ht

/-- Only m-th roots of unity occur in the simultaneous eigenspace decomposition.
Source: Schoen (1988), Lemma 1.2, pp. 5–6; eigenvalues of a finite-order operator. -/
theorem s4_e1_simultaneous_root_decomposition
    {ι V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : ι → Module.End ℂ V) {m : ℕ} (hm : 0 < m)
    [DecidableEq (ι → rootsOfUnity m ℂ)]
    (hf : ∀ i, f i ^ m = 1) (hcomm : ∀ i j, Commute (f i) (f j)) :
    DirectSum.IsInternal (fun c : ι → rootsOfUnity m ℂ =>
      ⨅ i, Module.End.eigenspace (f i) ((c i : ℂˣ) : ℂ)) := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  have hall := s4_e1_simultaneous_eigenspace_decomposition f hm hf hcomm
  have hparts := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hall
  have hinj : Function.Injective
      (fun c : ι → rootsOfUnity m ℂ => fun i => ((c i : ℂˣ) : ℂ)) := by
    intro c d h
    funext i
    apply Subtype.ext
    apply Units.ext
    exact congrFun h i
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨hparts.1.comp hinj, ?_⟩
  rw [eq_top_iff, ← hparts.2]
  refine iSup_le fun c v hv => ?_
  by_cases hv0 : v = 0
  · subst v
    exact Submodule.zero_mem _
  have hc (i : ι) : c i ^ m = 1 := by
    have he := (Module.End.hasEigenvector_iff.mpr
      ⟨(Submodule.mem_iInf _).mp hv i, hv0⟩).pow_apply m
    rw [hf i, Module.End.one_apply] at he
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp (show (c i ^ m - 1) • v = 0 by
      rw [sub_smul, ← he, one_smul, sub_self])).resolve_right hv0
  let r (i : ι) : rootsOfUnity m ℂ := rootsOfUnity.mkOfPowEq (c i) (hc i)
  exact Submodule.mem_iSup_of_mem r (by
    simpa only [r, rootsOfUnity.coe_mkOfPowEq] using hv)

#print axioms s4_e1_finite_order_semisimple
#print axioms s4_e1_simultaneous_eigenspace_decomposition
#print axioms s4_e1_simultaneous_root_decomposition
end HodgeLean.Foundations.Program
