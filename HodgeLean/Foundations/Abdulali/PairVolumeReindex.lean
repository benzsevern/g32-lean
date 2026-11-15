import HodgeLean.Foundations.Abdulali.PairVolumeCopyLabels
import HodgeLean.Foundations.Abdulali.TensorSumReindex

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A sum-slot enumeration differs from the standard append enumeration by one permutation. -/
theorem tensorSum_reindex_eq_perm_append (k l : ℕ)
    (e : (Fin k ⊕ Fin l) ≃ Fin (k + l))
    (a : ⨂[ℂ]^k V) (b : ⨂[ℂ]^l V) :
    PiTensorProduct.reindex ℂ (fun _ : Fin k ⊕ Fin l => V) e
      ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] b)) =
    SchurWeyl.permRep ℂ V _ (finSumFinEquiv.symm.trans e)
      (InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b)) := by
  have he : (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).trans
      (finSumFinEquiv.symm.trans e) = e := by
    ext x
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change PiTensorProduct.reindex ℂ _ e ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] b)) =
    PiTensorProduct.reindex ℂ _ (finSumFinEquiv.symm.trans e)
      (PiTensorProduct.reindex ℂ _ finSumFinEquiv
        ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] b)))
  have hr := PiTensorProduct.reindex_reindex (R := ℂ)
    (s := fun _ : Fin k ⊕ Fin l => V) finSumFinEquiv (finSumFinEquiv.symm.trans e)
    ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] b))
  simpa only [he] using hr.symm

variable [FiniteDimensional ℂ V]

/-- Any enumeration of a finite quadratic block and a volume block gives prescribed volume products. -/
theorem copyTensorIn_reindex_fin_volume_mem (B : LinearMap.BilinForm ℂ V) (r k n : ℕ)
    (e : (Fin k ⊕ Fin (Module.finrank ℂ V)) ≃ Fin n)
    (a : ⨂[ℂ]^k V) (ha : a ∈ m1b_products (m1b_fixed (m1b_isometries B) 2) k)
    (c : Fin n → Fin r) :
    m1b_copyTensorIn r n c
      (PiTensorProduct.reindex ℂ (fun _ : Fin k ⊕ Fin (Module.finrank ℂ V) => V) e
        ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V))) ∈
      orthogonalVolumeProducts B r n := by
  have hn : k + Module.finrank ℂ V = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  subst n
  rw [tensorSum_reindex_eq_perm_append]
  exact copyTensorIn_perm_append_volume_mem B r k a ha c _

/-- The retained quadratic block may carry any finite indexing type. -/
theorem copyTensorIn_reindex_volume_mem {A : Type*} [Fintype A] [DecidableEq A]
    (B : LinearMap.BilinForm ℂ V) (r n : ℕ)
    (e : (A ⊕ Fin (Module.finrank ℂ V)) ≃ Fin n)
    (a : ⨂[ℂ] (_ : A), V)
    (ha : PiTensorProduct.reindex ℂ (fun _ : A => V) (Fintype.equivFin A) a ∈
      m1b_products (m1b_fixed (m1b_isometries B) 2) (Fintype.card A))
    (c : Fin n → Fin r) :
    m1b_copyTensorIn r n c
      (PiTensorProduct.reindex ℂ (fun _ : A ⊕ Fin (Module.finrank ℂ V) => V) e
        ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V))) ∈
      orthogonalVolumeProducts B r n := by
  let aE := Fintype.equivFin A
  let e0 := (Equiv.sumCongr aE.symm (Equiv.refl (Fin (Module.finrank ℂ V)))).trans e
  have he : (Equiv.sumCongr aE (Equiv.refl (Fin (Module.finrank ℂ V)))).trans e0 = e := by
    ext x
    cases x <;> simp [e0]
  have ht : PiTensorProduct.reindex ℂ (fun _ : A ⊕ Fin (Module.finrank ℂ V) => V) e
      ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V)) =
      PiTensorProduct.reindex ℂ _ e0
        ((PiTensorProduct.tmulEquiv ℂ V)
          (PiTensorProduct.reindex ℂ (fun _ : A => V) aE a ⊗ₜ[ℂ]
            SchurWeyl.detTensorDual ℂ V)) := by
    have hr := PiTensorProduct.reindex_reindex (R := ℂ)
      (s := fun _ : A ⊕ Fin (Module.finrank ℂ V) => V)
      (Equiv.sumCongr aE (Equiv.refl (Fin (Module.finrank ℂ V)))) e0
      ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V))
    rw [he] at hr
    rw [← hr, tensorSum_reindex_left]
  rw [ht]
  exact copyTensorIn_reindex_fin_volume_mem B r (Fintype.card A) n e0 _ ha c

end HodgeLean.Foundations.Abdulali
