import HodgeLean.Foundations.Program.MilneTensorPairSlots
import HodgeLean.Foundations.Program.MilneTensorContractions

noncomputable section
open scoped Classical
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V β : Type*} [AddCommGroup V] [Module ℂ V] [Fintype β]

/-- The tensor obtained by assigning a common basis index to the two ends of every pair. -/
def pairingDiagram {P S : Type*} [Fintype P] [DecidableEq P] (b : β → V) (e : (P × Fin 2) ≃ S) :
    ⨂[ℂ] (_ : S), V :=
  ∑ f : P → β, PiTensorProduct.tprod ℂ (fun s => b (f (e.symm s).1))

/-- Reindexing the slots reindexes the encoded pairing. -/
theorem pairingDiagram_perm {P S : Type*} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S]
    (b : β → V) (e : (P × Fin 2) ≃ S) (σ : Equiv.Perm S) :
    SchurWeyl.permRep ℂ V S σ (pairingDiagram b e) = pairingDiagram b (e.trans σ) := by
  simp only [pairingDiagram, map_sum, SchurWeyl.permRep_tprod, Equiv.symm_trans_apply]

/-- Append one two-slot block to an existing pairing enumeration. -/
def pairingAppendEquiv (m n : ℕ) (e : (Fin m × Fin 2) ≃ Fin n) :
    (Fin (m + 1) × Fin 2) ≃ Fin (n + 2) :=
  (m1b_pairSlotsLast m).symm.trans
    ((Equiv.sumCongr e (Equiv.refl (Fin 2))).trans finSumFinEquiv)

/-- Appending a diagonal quadratic adds one pair to the pairing diagram. -/
theorem pairingDiagram_append (m n : ℕ) (b : β → V)
    (e : (Fin m × Fin 2) ≃ Fin n) :
    pairingDiagram b (pairingAppendEquiv m n e) =
      InvariantsExterior.tensorAppend n 2
        (pairingDiagram b e ⊗ₜ[ℂ] (∑ a : β, PiTensorProduct.tprod ℂ (fun _ : Fin 2 => b a))) := by
  unfold pairingDiagram
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => β)).sum_comp
    (fun f : Fin (m + 1) → β => PiTensorProduct.tprod ℂ
      (fun s => b (f ((pairingAppendEquiv m n e).symm s).1)))]
  simp only [Fintype.sum_prod_type, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    map_sum, InvariantsExterior.tensorAppend_tprod]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  funext s
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairingAppendEquiv m n e).surjective s
  simp only [Equiv.symm_apply_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [pairingAppendEquiv, m1b_pairSlotsLast, Fin.append, Fin.snoc]
  · simp [pairingAppendEquiv, m1b_pairSlotsLast, Fin.append, Fin.snoc]

end HodgeLean.Foundations.Abdulali
