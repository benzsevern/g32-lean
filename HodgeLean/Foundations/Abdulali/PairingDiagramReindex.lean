import HodgeLean.Foundations.Abdulali.PairingDiagram

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Abdulali

/-- Reindexing the output slots transports the pairing enumeration. -/
theorem pairingDiagram_reindex {P S T β V : Type*}
    [Fintype P] [DecidableEq P] [Fintype β] [AddCommGroup V] [Module ℂ V]
    (b : β → V) (e : (P × Fin 2) ≃ S) (a : S ≃ T) :
    PiTensorProduct.reindex ℂ (fun _ : S => V) a (pairingDiagram b e) =
      pairingDiagram b (e.trans a) := by
  simp only [pairingDiagram, map_sum, PiTensorProduct.reindex_tprod, Equiv.symm_trans_apply]

end HodgeLean.Foundations.Abdulali
