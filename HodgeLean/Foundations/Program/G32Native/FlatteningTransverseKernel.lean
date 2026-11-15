import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Kernel and surjectivity of the transverse flattening projection

The given flattening sends the actual tangent parametrization to the
zero-normal coordinate plane.
-/

noncomputable section
namespace HodgeLean.Foundations.TubularEuler
open Filter Topology

theorem flattening_transverse_kernel
    {K E B N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup B] [Module K B]
    [AddCommGroup N] [Module K N]
    (A : E ≃ₗ[K] B × N) (S : B →ₗ[K] E)
    (hS : ∀ b, A (S b) = (b, 0)) :
    ((LinearMap.snd K B N).comp A.toLinearMap).ker = S.range ∧
      Function.Surjective ((LinearMap.snd K B N).comp A.toLinearMap) := by
  constructor
  · ext w
    constructor
    · intro hw
      change (A w).2 = 0 at hw
      refine ⟨(A w).1, A.injective ?_⟩
      rw [hS]
      exact Prod.ext rfl hw.symm
    · rintro ⟨b, rfl⟩
      change (A (S b)).2 = 0
      rw [hS]
  · intro n
    refine ⟨A.symm (0, n), ?_⟩
    change (A (A.symm (0, n))).2 = n
    rw [A.apply_symm_apply]

#print axioms flattening_transverse_kernel

theorem transverse_kernel_eq_of_dimension
    {K E B N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (S : B →ₗ[K] E) (P : E →ₗ[K] N)
    (hS : Function.Injective S) (hP : Function.Surjective P)
    (hPS : P.comp S = 0)
    (hdim : Module.finrank K E = Module.finrank K B + Module.finrank K N) :
    P.ker = S.range := by
  have hle : S.range ≤ P.ker := by
    rintro _ ⟨b, rfl⟩
    exact LinearMap.congr_fun hPS b
  have hnull := P.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hP, finrank_top] at hnull
  have hker : Module.finrank K P.ker = Module.finrank K B := by omega
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.finrank_range_of_inj hS, hker]

#print axioms transverse_kernel_eq_of_dimension

theorem flattened_tangent_transverse_derivative_zero
    {K E B N : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup B] [NormedSpace K B]
    [NormedAddCommGroup N] [NormedSpace K N]
    (σ : B → E) (a : E → B × N) (b : B)
    (S : B →L[K] E) (A : E →L[K] B × N)
    (hσ : HasFDerivAt σ S b) (ha : HasFDerivAt a A (σ b))
    (hzero : ∀ᶠ u in 𝓝 b, (a (σ u)).2 = 0) :
    ((ContinuousLinearMap.snd K B N).comp A).comp S = 0 := by
  have hcomp := (ha.comp b hσ).snd
  have hz0 : HasFDerivAt (fun _ : B => (0 : N)) (0 : B →L[K] N) b :=
    hasFDerivAt_const (0 : N) b
  have hz : HasFDerivAt (fun u : B => (a (σ u)).2) 0 b :=
    hz0.congr_of_eventuallyEq hzero
  exact hcomp.unique hz

#print axioms flattened_tangent_transverse_derivative_zero
end HodgeLean.Foundations.TubularEuler
