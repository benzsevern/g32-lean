import HodgeLean.Foundations.Program.MilneTensorPairSlots
import HodgeLean.Foundations.Program.MilneTensorContractions

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V β : Type*} [AddCommGroup V] [Module ℂ V] [Fintype β]

theorem m1b_products_pairSums (Q : Submodule ℂ (⨂[ℂ]^2 V)) (k : ℕ)
    (v : Fin k → β → Fin 2 → V) (hv : ∀ i, (∑ b, ⨂ₜ[ℂ] s, v i b s) ∈ Q)
    (e : (Fin k × Fin 2) ≃ Fin (k * 2)) :
    (∑ f : Fin k → β, ⨂ₜ[ℂ] s, v (e.symm s).1 (f (e.symm s).1) (e.symm s).2) ∈
      m1b_products Q (k * 2) := by
  classical
  induction k with
  | zero => exact Submodule.mem_top
  | succ k ih =>
    revert e
    rw [Nat.succ_mul]
    intro e
    let e₀ : ((Fin k × Fin 2) ⊕ Fin 2) ≃ Fin (k * 2 + 2) :=
      (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans finSumFinEquiv
    let σ : Equiv.Perm (Fin (k * 2 + 2)) := e₀.symm.trans ((m1b_pairSlotsLast k).trans e)
    let a : ⨂[ℂ]^(k * 2) V := ∑ f : Fin k → β,
      ⨂ₜ[ℂ] s, v (finProdFinEquiv.symm s).1.castSucc
        (f (finProdFinEquiv.symm s).1) (finProdFinEquiv.symm s).2
    let b : ⨂[ℂ]^2 V := ∑ c, ⨂ₜ[ℂ] s, v (Fin.last k) c s
    have ha : a ∈ m1b_products Q (k * 2) :=
      ih (fun i => v i.castSucc) (fun i => hv i.castSucc) finProdFinEquiv
    have hb : b ∈ Q := hv (Fin.last k)
    have hp : SchurWeyl.permRep ℂ V (Fin (k * 2 + 2)) σ
        (InvariantsExterior.tensorAppend (k * 2) 2 (a ⊗ₜ[ℂ] b)) ∈
        m1b_products Q (k * 2 + 2) := Submodule.subset_span ⟨σ, a, b, ha, hb, rfl⟩
    convert hp using 1
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => β)).sum_comp]
    simp only [a, b, Fintype.sum_prod_type, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
      map_sum, InvariantsExterior.tensorAppend_tprod, SchurWeyl.permRep_tprod]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    funext s
    obtain ⟨z, rfl⟩ := σ.surjective s
    simp only [Equiv.symm_apply_apply]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) z
    · simp [σ, e₀, m1b_pairSlotsLast, Fin.append, Fin.snoc,
        show j.val / 2 < k from (j.divNat : Fin k).isLt]
    · simp [σ, e₀, m1b_pairSlotsLast, Fin.append, Fin.snoc]

end HodgeLean.Foundations.Program
