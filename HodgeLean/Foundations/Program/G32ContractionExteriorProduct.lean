import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basic

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem g32c_tmul_ne_zero {x : V} {y : W} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[K] y ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one K hy
  intro h
  have hh := congrArg (TensorProduct.lift (LinearMap.smulRight f g)) h
  simp only [TensorProduct.lift.tmul, LinearMap.smulRight_apply, LinearMap.smul_apply,
    smul_eq_mul, hf, hg, mul_one, map_zero] at hh
  exact one_ne_zero hh

theorem g32c_exterior_inl_mul_inr_ne_zero {x : ExteriorAlgebra K V} {y : ExteriorAlgebra K W}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ExteriorAlgebra.map (LinearMap.inl K V W) x *
      ExteriorAlgebra.map (LinearMap.inr K V W) y ≠ 0 := by
  rw [← ExteriorAlgebra.prodEquivTensor_symm_tmul]
  intro h
  have hh := congrArg (ExteriorAlgebra.prodEquivTensor K V W) h
  rw [AlgEquiv.apply_symm_apply, map_zero] at hh
  have ht := congrArg
    (GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i V) (fun i : ℕ => ⋀[K]^i W)).symm hh
  rw [GradedTensorProduct.tmul, LinearEquiv.symm_apply_apply, map_zero] at ht
  exact g32c_tmul_ne_zero hx hy ht

def g32c_piSuccEquiv {r : ℕ} (N : Fin (r + 1) → Type*)
    [∀ j, AddCommGroup (N j)] [∀ j, Module K (N j)] :
    (∀ j, N j) ≃ₗ[K] N 0 × (∀ j : Fin r, N j.succ) where
  toFun x := (x 0, fun j => x j.succ)
  invFun p := Fin.cases p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem g32c_orderedProduct_ne_zero {r : ℕ} (N : Fin r → Type*)
    [∀ j, AddCommGroup (N j)] [∀ j, Module K (N j)]
    (x : ∀ j, ExteriorAlgebra K (N j)) (hx : ∀ j, x j ≠ 0) :
    (List.ofFn fun j => ExteriorAlgebra.map (LinearMap.single K N j) (x j)).prod ≠ 0 := by
  induction r with
  | zero => simpa only [List.ofFn_zero, List.prod_nil] using
      (one_ne_zero : (1 : ExteriorAlgebra K (∀ j : Fin 0, N j)) ≠ 0)
  | succ r ih =>
      let e := g32c_piSuccEquiv (K := K) N
      have h0 : e.toLinearMap ∘ₗ LinearMap.single K N 0 =
          LinearMap.inl K (N 0) (∀ j : Fin r, N j.succ) := by
        apply LinearMap.ext
        intro z
        apply Prod.ext
        · simp [e, g32c_piSuccEquiv]
        · funext j
          simp [e, g32c_piSuccEquiv]
      have hj (j : Fin r) : e.toLinearMap ∘ₗ LinearMap.single K N j.succ =
          LinearMap.inr K (N 0) (∀ j : Fin r, N j.succ) ∘ₗ
            LinearMap.single K (fun j : Fin r => N j.succ) j := by
        apply LinearMap.ext
        intro z
        apply Prod.ext
        · simp [e, g32c_piSuccEquiv]
        · funext k
          simp only [e, g32c_piSuccEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
            AddHom.coe_mk, LinearMap.comp_apply, LinearMap.single_apply, LinearMap.inr_apply]
          by_cases h : k = j
          · subst k; simp
          · have h' : k.succ ≠ j.succ := by simpa only [ne_eq, Fin.succ_inj] using h
            simp [Pi.single_apply, h, h', Ne.symm h, Ne.symm h']
      have h0x : ExteriorAlgebra.map e.toLinearMap
          (ExteriorAlgebra.map (LinearMap.single K N 0) (x 0)) =
          ExteriorAlgebra.map (LinearMap.inl K (N 0) (∀ j : Fin r, N j.succ)) (x 0) := by
        change ((ExteriorAlgebra.map e.toLinearMap).comp
          (ExteriorAlgebra.map (LinearMap.single K N 0))) (x 0) = _
        rw [ExteriorAlgebra.map_comp_map, h0]
      have htail (j : Fin r) : ExteriorAlgebra.map e.toLinearMap
          (ExteriorAlgebra.map (LinearMap.single K N j.succ) (x j.succ)) =
          ExteriorAlgebra.map (LinearMap.inr K (N 0) (∀ j : Fin r, N j.succ))
            (ExteriorAlgebra.map (LinearMap.single K (fun j : Fin r => N j.succ) j) (x j.succ)) := by
        change ((ExteriorAlgebra.map e.toLinearMap).comp
          (ExteriorAlgebra.map (LinearMap.single K N j.succ))) (x j.succ) =
          ((ExteriorAlgebra.map (LinearMap.inr K (N 0) (∀ j : Fin r, N j.succ))).comp
            (ExteriorAlgebra.map (LinearMap.single K (fun j : Fin r => N j.succ) j))) (x j.succ)
        rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, hj]
      have hprod : ExteriorAlgebra.map e.toLinearMap
          (List.ofFn fun j => ExteriorAlgebra.map (LinearMap.single K N j) (x j)).prod =
          ExteriorAlgebra.map (LinearMap.inl K (N 0) (∀ j : Fin r, N j.succ)) (x 0) *
            ExteriorAlgebra.map (LinearMap.inr K (N 0) (∀ j : Fin r, N j.succ))
              (List.ofFn fun j : Fin r =>
                ExteriorAlgebra.map (LinearMap.single K (fun j : Fin r => N j.succ) j) (x j.succ)).prod := by
        simp only [List.ofFn_succ, List.prod_cons, map_mul]
        rw [h0x]
        congr 1
        simp only [map_list_prod, List.map_ofFn, Function.comp_def]
        exact congrArg List.prod (congrArg List.ofFn (funext htail))
      intro hz
      have hh := congrArg (ExteriorAlgebra.map e.toLinearMap) hz
      rw [hprod, map_zero] at hh
      exact g32c_exterior_inl_mul_inr_ne_zero (hx 0)
        (ih (fun j : Fin r => N j.succ) (fun j => x j.succ) (fun j => hx j.succ)) hh

end HodgeLean.Foundations.Program
