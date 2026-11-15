import HodgeLean.Foundations.Program.SchoenTransferTensorOperatorRelations
import HodgeLean.Foundations.Program.SchoenTransferTensorSubspaceLift
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

noncomputable section
set_option maxHeartbeats 200000
open Polynomial
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program

/-- Equal coordinate equations and alternating permutation equations persist under a coordinate operator. -/
theorem s4_equal_alternating_tensor_stable {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (n : ℕ) (A : Module.End K V) (j : Fin n)
    {z : ⨂[K] i : Fin n, V}
    (hz : ∀ i, s4_tensorCoordinate A i z = s4_tensorCoordinate A j z)
    (hσ : ∀ σ : Equiv.Perm (Fin n), s4_tensorPermutation n σ z = σ.sign • z) :
    (∀ i, s4_tensorCoordinate A i (s4_tensorCoordinate A j z) =
      s4_tensorCoordinate A j (s4_tensorCoordinate A j z)) ∧
    (∀ σ : Equiv.Perm (Fin n), s4_tensorPermutation n σ (s4_tensorCoordinate A j z) =
      σ.sign • s4_tensorCoordinate A j z) := by
  constructor
  · intro i
    rw [← LinearMap.comp_apply, s4_tensorCoordinate_commute, LinearMap.comp_apply, hz i]
  · intro σ
    rw [← LinearMap.comp_apply, s4_tensorPermutation_coordinate, LinearMap.comp_apply,
      hσ, Units.smul_def, map_zsmul, hz (σ.symm j)]
    rfl

/-- A polynomial kernel is stable under its defining endomorphism. -/
theorem s4_polynomial_kernel_stable {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (A : Module.End K V) (P : K[X])
    {z : V} (hz : Polynomial.aeval A P z = 0) : Polynomial.aeval A P (A z) = 0 := by
  have he := (Commute.all P Polynomial.X).map (Polynomial.aeval A)
  rw [Polynomial.aeval_X] at he
  change (Polynomial.aeval A P).comp A = A.comp (Polynomial.aeval A P) at he
  rw [← LinearMap.comp_apply, he, LinearMap.comp_apply, hz, map_zero]

/-- Polynomial primitive alternating tensors with equal coordinate actions are exhausted by exterior eigenspaces. -/
theorem s4_primitive_tensor_exhaustion {K V B : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype B]
    (b : Module.Basis B K V) (A : Module.End K V) (c : B → K)
    (hA : ∀ i, A (b i) = c i • b i) (n : ℕ) (j : Fin n) (P : K[X])
    {z : ⨂[K] i : Fin n, V}
    (hP : Polynomial.aeval (s4_tensorCoordinate A j) P z = 0)
    (hz : ∀ i, s4_tensorCoordinate A i z = s4_tensorCoordinate A j z)
    (hσ : ∀ σ : Equiv.Perm (Fin n), s4_tensorPermutation n σ z = σ.sign • z) :
    z ∈ ⨆ μ : {μ : K // P.IsRoot μ}, LinearMap.range
      ((exteriorPower.toTensorPower K V n).comp
        (exteriorPower.map n (Module.End.eigenspace A μ.val).subtype)) := by
  classical
  let R := s4_tensorCoordinate A j
  let U : Submodule K (⨂[K] i : Fin n, V) :=
    LinearMap.ker (Polynomial.aeval R P) ⊓
      (⨅ i : Fin n, LinearMap.ker (s4_tensorCoordinate A i - R)) ⊓
      ⨅ σ : Equiv.Perm (Fin n), LinearMap.ker (s4_tensorPermutation n σ - σ.sign • LinearMap.id)
  have hU (x : ⨂[K] i : Fin n, V) : x ∈ U ↔
      Polynomial.aeval R P x = 0 ∧
      (∀ i, s4_tensorCoordinate A i x = R x) ∧
      (∀ σ : Equiv.Perm (Fin n), s4_tensorPermutation n σ x = σ.sign • x) := by
    simp only [U, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, s4_linearMap_unit_apply, LinearMap.id_apply, sub_eq_zero,
      and_assoc]
  have hstable : ∀ x ∈ U, R x ∈ U := by
    intro x hx
    obtain ⟨hp, hc, hs⟩ := (hU x).mp hx
    have ht := s4_equal_alternating_tensor_stable n A j hc hs
    exact (hU _).mpr ⟨s4_polynomial_kernel_stable R P hp, ht.1, ht.2⟩
  have hcover : (⨆ μ : K, Module.End.eigenspace R μ) = ⊤ := by
    apply top_unique
    rw [← (Basis.piTensorProduct (fun _ : Fin n => b)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact Submodule.mem_iSup_of_mem (c (p j))
      (Module.End.mem_eigenspace_iff.mpr (s4_tensorCoordinate_basis b A c hA j p))
  have hdecomp := Submodule.inf_iSup_genEigenspace (p := U) (f := R) hstable 1
  change U ⊓ (⨆ μ : K, Module.End.eigenspace R μ) =
    (⨆ μ : K, U ⊓ Module.End.eigenspace R μ) at hdecomp
  rw [hcover, inf_top_eq] at hdecomp
  have hin : z ∈ U := (hU z).mpr ⟨hP, hz, hσ⟩
  rw [hdecomp] at hin
  suffices hle : (⨆ μ : K, U ⊓ Module.End.eigenspace R μ) ≤
      (⨆ μ : {μ : K // P.IsRoot μ}, LinearMap.range
        ((exteriorPower.toTensorPower K V n).comp
          (exteriorPower.map n (Module.End.eigenspace A μ.val).subtype))) by
    exact hle hin
  apply iSup_le
  intro μ
  rintro x ⟨hxU, hxR⟩
  obtain ⟨hp, hc, hs⟩ := (hU x).mp hxU
  have heig : R x = μ • x := Module.End.mem_eigenspace_iff.mp hxR
  by_cases hx : x = 0
  · subst x; exact Submodule.zero_mem _
  have hroot : P.IsRoot μ := by
    have he := Module.End.aeval_apply_of_mem_apply_eq_smul (p := P) heig
    rw [hp] at he
    exact (smul_eq_zero.mp he.symm).resolve_right hx
  have hsupport := s4_tensor_eigen_support b A c hA μ x (fun i => (hc i).trans heig)
  exact Submodule.mem_iSup_of_mem ⟨μ, hroot⟩
    (s4_alternating_tensor_subspace_lift n (Module.End.eigenspace A μ) hsupport hs)

end HodgeLean.Foundations.Program
