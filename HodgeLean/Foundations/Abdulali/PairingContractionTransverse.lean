import HodgeLean.Foundations.Abdulali.PairingDiagramSplit
import HodgeLean.Foundations.Abdulali.AlternatingDiagonalSum

noncomputable section
open scoped TensorProduct Classical
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- A transverse pairing diagram contracts to a remaining pairing tensor times one volume. -/
theorem pairingDiagram_transverse_volume {P I V : Type*}
    [Fintype P] [DecidableEq P] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : (P × Fin 2) ≃ (I ⊕ Fin (Module.finrank ℂ V)))
    (f : Fin (Module.finrank ℂ V) ↪ I)
    (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j))
    (b : Fin (Module.finrank ℂ V) → V) :
    (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id normalizedVolumeCovector
      ((PiTensorProduct.tmulEquiv ℂ V).symm (pairingDiagram b e))) =
    (normalizedVolumeCovector (PiTensorProduct.tprod ℂ b) * (Module.finBasis ℂ V).det b) •
      PiTensorProduct.reindex ℂ
        (fun _ : (RemainingPairBlocks e × Fin 2) ⊕ Fin (Module.finrank ℂ V) => V)
        (pairingRetainedEquiv e f hf)
        ((PiTensorProduct.tmulEquiv ℂ V)
          (pairingDiagram b (Equiv.refl (RemainingPairBlocks e × Fin 2)) ⊗ₜ[ℂ]
            SchurWeyl.detTensorDual ℂ V)) := by
  rw [pairingDiagram_contract_split e f hf b normalizedVolumeCovector,
    normalizedVolumeCovector_diagonal_sum, antisymTensor_eq_det_smul_volume,
    smul_smul, TensorProduct.tmul_smul, map_smul, map_smul]

end HodgeLean.Foundations.Abdulali
