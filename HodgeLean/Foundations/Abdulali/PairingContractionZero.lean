import HodgeLean.Foundations.Abdulali.PairingDiagram
import HodgeLean.Foundations.Abdulali.AlternatingDiagonalSum
import HodgeLean.Foundations.Abdulali.PairingIndexSplit

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- A pairing block joining two extra slots has zero normalized volume contraction. -/
theorem pairingDiagram_contraction_eq_zero_of_extra_pair
    {P I β V : Type*} [Fintype P] [DecidableEq P] [Fintype β]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : β → V) (e : (P × Fin 2) ≃ (I ⊕ Fin (Module.finrank ℂ V)))
    (i j : Fin (Module.finrank ℂ V)) (hij : i ≠ j)
    (h : (e.symm (Sum.inr i)).1 = (e.symm (Sum.inr j)).1) :
    (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id normalizedVolumeCovector
      ((PiTensorProduct.tmulEquiv ℂ V).symm (pairingDiagram b e))) = 0 := by
  simp only [pairingDiagram, map_sum, PiTensorProduct.tmulEquiv_symm_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul]
  apply Finset.sum_eq_zero
  intro a _
  rw [normalizedVolumeCovector_tprod_eq_zero_of_eq _ i j hij
    (congrArg (fun p => b (a p)) h), zero_smul]

end HodgeLean.Foundations.Abdulali
