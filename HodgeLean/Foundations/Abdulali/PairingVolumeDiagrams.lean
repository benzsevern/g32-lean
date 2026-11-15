import HodgeLean.Foundations.Abdulali.PairingContractionZero
import HodgeLean.Foundations.Abdulali.PairingContractionTransverse
import HodgeLean.Foundations.Abdulali.PairingDiagramProducts
import HodgeLean.Foundations.Abdulali.PairingDiagramReindex
import HodgeLean.Foundations.Abdulali.PairVolumeReindex
import HodgeLean.Foundations.Abdulali.BaseTensorContraction

noncomputable section
open scoped TensorProduct Classical
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- Every pairing diagram contracts into the prescribed independently labeled volume products. -/
theorem pairingDiagram_volume_contract_mem {P V : Type*}
    [Fintype P] [DecidableEq P] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (r n : ℕ)
    (b : Fin (Module.finrank ℂ V) → V)
    (hq : (∑ a : Fin (Module.finrank ℂ V), PiTensorProduct.tprod ℂ (fun _ : Fin 2 => b a)) ∈
      m1b_fixed (m1b_isometries B) 2)
    (e : (P × Fin 2) ≃ Fin (n + Module.finrank ℂ V)) (c : Fin n → Fin r) :
    m1b_copyTensorIn r n c
      (baseTensorContraction n (Module.finrank ℂ V) normalizedVolumeCovector
        (pairingDiagram b e)) ∈ orthogonalVolumeProducts B r n := by
  let E := e.trans (finSumFinEquiv : Fin n ⊕ Fin (Module.finrank ℂ V) ≃ _).symm
  have he : baseTensorContraction n (Module.finrank ℂ V) normalizedVolumeCovector
      (pairingDiagram b e) =
      (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id normalizedVolumeCovector
        ((PiTensorProduct.tmulEquiv ℂ V).symm (pairingDiagram b E))) := by
    rw [baseTensorContraction_eq_reindex, pairingDiagram_reindex]
  rw [he]
  rcases pairingPartner_split E with ⟨i, j, hij, hp⟩ | ⟨f, hf⟩
  · have hi : (E.symm (Sum.inr i)).1 = (E.symm (Sum.inr j)).1 := by
      have h := pairingIndex_partner E (Sum.inr i)
      rw [hp] at h
      exact h.symm
    rw [pairingDiagram_contraction_eq_zero_of_extra_pair b E i j hij hi, map_zero]
    exact Submodule.zero_mem _
  · rw [pairingDiagram_transverse_volume E f hf b, map_smul]
    apply Submodule.smul_mem
    apply copyTensorIn_reindex_volume_mem B r n (pairingRetainedEquiv E f hf)
    rw [pairingDiagram_reindex]
    exact pairingDiagram_mem_products b _ _ (m1b_fixed (m1b_isometries B) 2) hq

end HodgeLean.Foundations.Abdulali
