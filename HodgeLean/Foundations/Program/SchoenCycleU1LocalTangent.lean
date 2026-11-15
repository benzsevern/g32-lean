import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Residue-field derivations and local unramifiedness -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Vanishing of residue-field derivations detects unramifiedness for an
essentially finite-type local algebra, by the cotangent universal property and Nakayama.
Source: Mathlib, `KaehlerDifferential.linearMapEquivDerivation`,
`IsLocalRing.subsingleton_tensorProduct`; Stacks Project, Tag 00UM. -/
theorem s2e_u1_local_unramified_of_residue_derivations
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing B] [Algebra.EssFiniteType A B]
    (hder : ∀ d : Derivation A B (IsLocalRing.ResidueField B), d = 0) :
    Algebra.FormallyUnramified A B := by
  let K := IsLocalRing.ResidueField B
  let T := K ⊗[B] KaehlerDifferential A B
  have hzero (φ : T →ₗ[K] K) : φ = 0 := by
    let f : KaehlerDifferential A B →ₗ[B] K :=
      (φ.restrictScalars B).comp (TensorProduct.mk B K (KaehlerDifferential A B) 1)
    have hf : f = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation A B (M := K)).injective
      exact (hder _).trans (map_zero _).symm
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero φ
    | tmul c ω =>
      have he : c ⊗ₜ[B] ω = c • ((1 : K) ⊗ₜ[B] ω) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, map_smul]
      have hw : φ ((1 : K) ⊗ₜ[B] ω) = 0 := congrArg (fun l => l ω) hf
      rw [hw, smul_zero]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy, add_zero, LinearMap.zero_apply]
  have hT : Subsingleton T := by
    apply subsingleton_of_forall_eq 0
    intro x
    apply (Module.forall_dual_apply_eq_zero_iff K x).mp
    intro φ
    rw [hzero φ]
    rfl
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := B)).mp hT⟩

end HodgeLean.Foundations.Program
