module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2e_linearEquiv_between_nonzero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ L : V ≃ₗ[K] V, L u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton K V u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton K V v hv
  obtain ⟨L, hL⟩ := Submodule.exists_linearEquiv_restrict_eq (eu.symm.trans ev)
  refine ⟨L, ?_⟩
  have h := hL (eu 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [eu, ev] using h.symm

end HodgeLean.Foundations.Program
