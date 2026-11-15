import HodgeLean.Foundations.Abdulali.PairingDiagram
import HodgeLean.Foundations.Abdulali.PairingRetainedSlots

noncomputable section
open scoped TensorProduct Classical
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- The block indices that do not meet an extra slot. -/
abbrev RemainingPairBlocks {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J)) :=
  {p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)}

/-- The retained pure tensor separates into remaining pair slots and crossing slots. -/
theorem pairing_retained_tprod {P I J β V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : (P × Fin 2) ≃ (I ⊕ J)) (f : J ↪ I)
    (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j))
    (b : β → V) (g : RemainingPairBlocks e → β) (h : J → β) :
    PiTensorProduct.tprod ℂ (fun i : I =>
      b (Sum.elim g h ((pairingBlockEquiv e f hf).symm (e.symm (Sum.inl i)).1))) =
    PiTensorProduct.reindex ℂ (fun _ : (RemainingPairBlocks e × Fin 2) ⊕ J => V)
      (pairingRetainedEquiv e f hf)
      (PiTensorProduct.tprod ℂ
        (Sum.elim (fun p : RemainingPairBlocks e × Fin 2 => b (g p.1)) (fun j => b (h j)))) := by
  rw [PiTensorProduct.reindex_tprod]
  congr 1
  funext i
  obtain ⟨x, rfl⟩ := (pairingRetainedEquiv e f hf).surjective i
  rw [pairingRetainedEquiv_index, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  cases x <;> rfl

/-- Splitting the block indices factors a pairing diagram into remaining and crossing assignments. -/
theorem pairingDiagram_split_sum {P I J β V : Type*}
    [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J] [Fintype β]
    [AddCommGroup V] [Module ℂ V]
    (e : (P × Fin 2) ≃ (I ⊕ J)) (f : J ↪ I)
    (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) (b : β → V) :
    (PiTensorProduct.tmulEquiv ℂ V).symm (pairingDiagram b e) =
      ∑ g : RemainingPairBlocks e → β, ∑ h : J → β,
        (PiTensorProduct.reindex ℂ (fun _ : (RemainingPairBlocks e × Fin 2) ⊕ J => V)
          (pairingRetainedEquiv e f hf)
          (PiTensorProduct.tprod ℂ
            (Sum.elim (fun p : RemainingPairBlocks e × Fin 2 => b (g p.1)) (fun j => b (h j))))) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (b ∘ h) := by
  let E : ((RemainingPairBlocks e → β) × (J → β)) ≃ (P → β) :=
    (Equiv.sumArrowEquivProdArrow (RemainingPairBlocks e) J β).symm.trans
      (Equiv.arrowCongr (pairingBlockEquiv e f hf) (Equiv.refl β))
  have he (g : RemainingPairBlocks e → β) (h : J → β) :
      E (g, h) = fun p => Sum.elim g h ((pairingBlockEquiv e f hf).symm p) := rfl
  rw [pairingDiagram, map_sum, ← E.sum_comp]
  simp only [Fintype.sum_prod_type, he, PiTensorProduct.tmulEquiv_symm_apply]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  rw [pairing_retained_tprod]
  congr 1
  congr 1
  funext j
  have hj : (e.symm (Sum.inr j)).1 = pairingBlockEquiv e f hf (Sum.inr j) := by
    rw [pairingBlockEquiv_apply]
    rfl
  rw [hj, Equiv.symm_apply_apply]
  rfl

/-- Contracting the extra block factors through the diagonal sum on crossing slots. -/
theorem pairingDiagram_contract_split {P I J β V : Type*}
    [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J] [Fintype β]
    [AddCommGroup V] [Module ℂ V]
    (e : (P × Fin 2) ≃ (I ⊕ J)) (f : J ↪ I)
    (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) (b : β → V)
    (ℓ : (⨂[ℂ] (_ : J), V) →ₗ[ℂ] ℂ) :
    (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id ℓ
      ((PiTensorProduct.tmulEquiv ℂ V).symm (pairingDiagram b e))) =
    PiTensorProduct.reindex ℂ (fun _ : (RemainingPairBlocks e × Fin 2) ⊕ J => V)
      (pairingRetainedEquiv e f hf)
      ((PiTensorProduct.tmulEquiv ℂ V)
        (pairingDiagram b (Equiv.refl (RemainingPairBlocks e × Fin 2)) ⊗ₜ[ℂ]
          (∑ h : J → β, ℓ (PiTensorProduct.tprod ℂ (b ∘ h)) • PiTensorProduct.tprod ℂ (b ∘ h)))) := by
  rw [pairingDiagram_split_sum e f hf b]
  simp only [pairingDiagram, map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul, TensorProduct.tmul_sum, TensorProduct.sum_tmul,
    TensorProduct.tmul_smul, map_smul, PiTensorProduct.tmulEquiv_apply]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum, Equiv.refl_symm, Equiv.refl_apply, Function.comp_def]

end HodgeLean.Foundations.Abdulali
