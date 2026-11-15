import HodgeLean.Foundations.Program.ComponentTransportUnlabelledChain
import HodgeLean.Foundations.Program.ComponentTransportUnlabelledClasses
import HodgeLean.Foundations.Program.BraidBridgesThreeFill
import HodgeLean.Foundations.Program.BraidCertificate

/-! # Relabelling edge and certificate endpoint: finite label data
The position permutation of a signed Hurwitz word, the slot permutation as an equivalence, and
the composed endpoint permutation of the certificate in branch-label coordinates. These are
finite definitions; no monodromy statement is made here.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- The transposition of tuple positions exchanged by one elementary move; a simultaneous
conjugation exchanges no positions.
Source: `b65s_step`; Völklein, *Groups as Galois Groups*, Chapters 9–10. -/
def b65u_moveSwap : b65s_Move → Equiv.Perm (Fin 13)
  | .positive i => Equiv.swap i.castSucc i.succ
  | .negative i => Equiv.swap i.castSucc i.succ
  | .conjugate _ => 1

example : b65u_moveSwap (.positive 0) 0 = 1 := by decide

/-- The position permutation of a finite word in list order: entry `k` of `b65s_word w t` is
conjugate to entry `b65u_movePerm w k` of `t`.
Source: `b65s_word`, `b65s_step`; Völklein, Chapters 9–10, composition of Hurwitz moves. -/
def b65u_movePerm : List b65s_Move → Equiv.Perm (Fin 13)
  | [] => 1
  | m :: w => b65u_moveSwap m * b65u_movePerm w

example : b65u_movePerm [] = 1 := rfl
example : b65u_movePerm b65b_pathWord 2 = 4 := by decide

/-- The slot convention `b65x_slot` as a permutation, with inverse `b65x_slotInv`.
Source: `b65x_slot` (`BraidBridgesDefs.lean`), `b65x_slotInv`, `b65x_slotInv_slot`,
`b65x_slot_slotInv` (`BraidBridgesThreeFill.lean`). -/
def b65u_slotPerm : Equiv.Perm (Fin 13) where
  toFun := b65x_slot
  invFun := b65x_slotInv
  left_inv := b65x_slotInv_slot
  right_inv := b65x_slot_slotInv

example : b65u_slotPerm 4 = 2 := rfl

/-- The composed source permutation of the certificate: the 86-move word acting on
`b65s_columnRoot` (`b65b_replay`) after undoing the two path moves acting on `b65b_initial`
(`b65b_path_replay`). Entry `i` of `b65b_initial` is conjugate to entry `b65u_sourcePerm i`
of `b65s_columnRoot`.
Source: `b65b_replay`, `b65b_path_replay`; `b65u_movePerm`. -/
def b65u_sourcePerm : Equiv.Perm (Fin 13) :=
  b65u_movePerm b65b_word * (b65u_movePerm b65b_pathWord)⁻¹

example : b65u_sourcePerm 2 = 7 := by decide +kernel

/-- The composed endpoint permutation in branch-label coordinates. Certified label `j` is the
puncture of slot `i = b65x_slotInv (12 - j)`; that slot carries `(b65b_initial i)⁻¹`, and the
reference label it meets is `12 - b65u_sourcePerm i`, because
`b65s_columnRoot k = (b4b_root (12 - k))⁻¹`.
Source: `b65u_sourcePerm`, `b65u_slotPerm`; `b65s_columnRoot` (`PullbackMonodromyDefs.lean`),
`b65b_lasso` (`BraidCertificateDefs.lean`), slot convention `j = 12 - b65x_slot i`. -/
def b65u_endpointPerm : Equiv.Perm (Fin 13) :=
  Fin.revPerm * b65u_sourcePerm * b65u_slotPerm⁻¹ * Fin.revPerm

example : List.ofFn b65u_endpointPerm = [4, 1, 0, 9, 2, 7, 3, 6, 10, 5, 11, 8, 12] := by
  decide +kernel

/-- The certified class at label `j` is the class of `b4b_root (b65u_endpointPerm j)`. -/
example : ∀ j : Fin 13, b65y_initialInvClasses (b65u_slotPerm.symm j.rev) =
    b65y_rootClasses (b65u_endpointPerm j) := by
  decide +kernel

end HodgeLean.Foundations.Program
