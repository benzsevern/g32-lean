import HodgeLean.Foundations.WeilPowerTransport

/-! # Scalar extension and the Hodge grading of Weil powers

These constructions support F-1575's transport from the invariant-theory lemma
at the level of `⋀ H¹`. The Hodge-group equality is an explicit input. C7 and
algebraicity of the generators are separate tasks.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
open InvariantsExterior
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

set_option maxHeartbeats 4000000 in
/-- Complexify each factor of a rational exterior power.
Source: constructed here using the universal alternating map. -/
def exteriorComplexify (k : ℕ) : (⋀[ℚ]^k V) →ₗ[ℚ] (⋀[ℂ]^k (ℂ ⊗[ℚ] V)) :=
  exteriorPower.alternatingMapLinearEquiv
    (({ toMultilinearMap :=
          (exteriorPower.ιMulti ℂ k).toMultilinearMap.restrictScalars ℚ
        map_eq_zero_of_eq' := (exteriorPower.ιMulti ℂ k).map_eq_zero_of_eq' } :
        (ℂ ⊗[ℚ] V) [⋀^Fin k]→ₗ[ℚ] (⋀[ℂ]^k (ℂ ⊗[ℚ] V))).compLinearMap
      (TensorProduct.mk ℚ ℂ V 1))

@[simp] theorem exteriorComplexify_ιMulti (k : ℕ) (v : Fin k → V) :
    exteriorComplexify k (exteriorPower.ιMulti ℚ k v) =
      exteriorPower.ιMulti ℂ k (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) := by
  rw [exteriorComplexify, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

example (v : Fin 2 → V) : exteriorComplexify 2 (exteriorPower.ιMulti ℚ 2 v) =
    exteriorPower.ιMulti ℂ 2 (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) := exteriorComplexify_ιMulti 2 v

variable [FiniteDimensional ℚ V]

/-- Scalar extension commutes with exterior powers.
Source: constructed here by comparing the exterior bases before and after scalar extension. -/
def exteriorBaseChange (k : ℕ) :
    (ℂ ⊗[ℚ] (⋀[ℚ]^k V)) ≃ₗ[ℂ] (⋀[ℂ]^k (ℂ ⊗[ℚ] V)) :=
  (((Module.finBasis ℚ V).exteriorPower k).baseChange ℂ).equiv
    (((Module.finBasis ℚ V).baseChange ℂ).exteriorPower k) (Equiv.refl _)

theorem exteriorBaseChange_eq_lift (k : ℕ) :
    (exteriorBaseChange (V := V) k).toLinearMap =
      (exteriorComplexify k).liftBaseChange ℂ := by
  apply (((Module.finBasis ℚ V).exteriorPower k).baseChange ℂ).ext
  intro s
  change (((Module.finBasis ℚ V).exteriorPower k).baseChange ℂ).equiv
    (((Module.finBasis ℚ V).baseChange ℂ).exteriorPower k) (Equiv.refl _)
      ((((Module.finBasis ℚ V).exteriorPower k).baseChange ℂ) s) = _
  rw [Module.Basis.equiv_apply, Module.Basis.baseChange_apply,
    LinearMap.liftBaseChange_tmul, one_smul]
  simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Function.comp_def]

@[simp] theorem exteriorBaseChange_one_ιMulti (k : ℕ) (v : Fin k → V) :
    exteriorBaseChange k ((1 : ℂ) ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ k v) =
      exteriorPower.ιMulti ℂ k (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) := by
  change (exteriorBaseChange k).toLinearMap _ = _
  rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul,
    exteriorComplexify_ιMulti]

example (k : ℕ) : Function.Bijective (exteriorBaseChange (V := V) k) :=
  (exteriorBaseChange k).bijective

theorem exteriorBaseChange_der (k : ℕ) (f : Module.End ℚ V) :
    (exteriorBaseChange k).toLinearMap.comp ((exteriorDer k f).baseChange ℂ) =
      (exteriorDer k (f.baseChange ℂ)).comp (exteriorBaseChange k).toLinearMap := by
  apply (((Module.finBasis ℚ V).exteriorPower k).baseChange ℂ).ext
  intro s
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorBaseChange_one_ιMulti, exteriorDer_ιMulti, TensorProduct.tmul_sum, map_sum,
    exteriorBaseChange_one_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h]

end HodgeLean.Foundations.WeilPower


noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower

variable {N : Type*} [AddCommGroup N] [Module ℚ N]

private theorem baseChange_iInf_fin (n : ℕ) (S : Fin n → Submodule ℚ N) :
    (⨅ i, S i).baseChange ℂ = ⨅ i, (S i).baseChange ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hq : (⨅ i, S i) = S 0 ⊓ ⨅ i : Fin n, S i.succ := by
      ext x
      simp [Fin.forall_fin_succ]
    rw [hq, baseChange_inf, ih]
    ext x
    simp [Fin.forall_fin_succ]

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  [LieRingModule (Module.End ℚ V) N] [LieModule ℚ (Module.End ℚ V) N]

private theorem invariants_eq_basis_kernels (L : LieSubalgebra ℚ (Module.End ℚ V)) :
    (LieModule.maxTrivSubmodule ℚ L N : Submodule ℚ N) =
      ⨅ i, LinearMap.ker (LieModule.toEnd ℚ (Module.End ℚ V) N
        ((Module.finBasis ℚ L i : L) : Module.End ℚ V)) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    exact h (Module.finBasis ℚ L i)
  · intro h X
    simp only [LieModule.toEnd_apply_apply] at h
    rw [← (Module.finBasis ℚ L).sum_repr X]
    simp only [sum_lie, smul_lie]
    simp [h]

/-- Extension of scalars commutes with invariants of a rational endomorphism Lie algebra.
Source: constructed here from finite intersections of kernels and flat scalar extension. -/
theorem mem_baseChange_invariants_iff
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (v : ℂ ⊗[ℚ] N) :
    v ∈ (LieModule.maxTrivSubmodule ℚ L N : Submodule ℚ N).baseChange ℂ ↔
      ∀ X ∈ complexSpan L.toSubmodule, complexAction N X v = 0 := by
  rw [invariants_eq_basis_kernels, baseChange_iInf_fin]
  simp only [Submodule.mem_iInf, ← ker_baseChange_eq, LinearMap.mem_ker]
  constructor
  · intro hv X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨Y, hY, rfl⟩ := hX
      let y : L := ⟨Y, hY⟩
      have hy : Y = ∑ i, ((Module.finBasis ℚ L).repr y i) •
          ((Module.finBasis ℚ L i : L) : Module.End ℚ V) := by
        simpa only [map_sum, map_smul, LieSubalgebra.coe_incl] using
          (congrArg L.incl ((Module.finBasis ℚ L).sum_repr y)).symm
      rw [hy]
      change complexAction N ((LinearMap.baseChangeHom ℚ ℂ V V) (∑ i, _)) v = 0
      rw [map_sum]
      simp only [map_sum, LinearMap.sum_apply, map_smul]
      apply Finset.sum_eq_zero
      intro i _
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]
      change ((Module.finBasis ℚ L).repr y i) •
        complexAction N (((Module.finBasis ℚ L i : L) : Module.End ℚ V).baseChange ℂ) v = 0
      rw [complexAction_baseChange (V := V), hv, smul_zero]
    | zero => simp
    | add X Y hX hY hx hy => simp [hx, hy]
    | smul c X hX hx => simp [hx]
  · intro hv i
    rw [← complexAction_baseChange]
    apply hv
    exact Submodule.subset_span ⟨_, (Module.finBasis ℚ L i).property, rfl⟩

end HodgeLean.Foundations.WeilPower
