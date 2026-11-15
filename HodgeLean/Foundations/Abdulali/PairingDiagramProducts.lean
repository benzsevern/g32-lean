import HodgeLean.Foundations.Abdulali.PairingDiagram
import HodgeLean.Foundations.Program.MilneTensorPairSums

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- A pairing diagram is a quadratic product whenever its diagonal pair belongs to the quadratic space. -/
theorem pairingDiagram_mem_products {P β V : Type*}
    [Fintype P] [DecidableEq P] [Fintype β] [AddCommGroup V] [Module ℂ V]
    (b : β → V) (n : ℕ) (e : (P × Fin 2) ≃ Fin n)
    (Q : Submodule ℂ (⨂[ℂ]^2 V))
    (hq : (∑ a : β, PiTensorProduct.tprod ℂ (fun _ : Fin 2 => b a)) ∈ Q) :
    pairingDiagram b e ∈ m1b_products Q n := by
  have hn : Fintype.card P * 2 = n := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr e
  subst n
  let a := Fintype.equivFin P
  let E := (Equiv.prodCongr a.symm (Equiv.refl (Fin 2))).trans e
  have hd : pairingDiagram b E = pairingDiagram b e := by
    unfold pairingDiagram
    apply Fintype.sum_equiv (Equiv.arrowCongr a.symm (Equiv.refl β))
    intro g
    congr 1
  rw [← hd]
  exact m1b_products_pairSums Q (Fintype.card P) (fun _ i _ => b i) (fun _ => hq) E

end HodgeLean.Foundations.Abdulali
