import HodgeLean.Foundations.Program.NumeratorJetBasisData
import HodgeLean.Foundations.Program.NumeratorJetDefs
import HodgeLean.Foundations.Program.KernelFramesFamilyMirror

/-! # Rational recursion checks for the eigenbasis jets -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- The stored eigenbasis jets satisfy the eigenvector recursion. -/
theorem b65e_basisJet_eig : ∀ k : Fin 4, ∀ n : Fin 8,
    ∑ a ∈ Finset.range (n.val + 1),
      b65e_fixedJet (Fin.ofNat 8 a) k * b65e_basisJetQ k (Fin.ofNat 8 (n.val - a)) =
    b65e_basisJetQ k n * diagonal (b65q_lamQ k) := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored eigenbasis jets satisfy the block normalization. -/
theorem b65e_basisJet_norm : ∀ k : Fin 4, ∀ n : Fin 8, ∀ i j : Fin 4,
    b65q_lamQ k i = b65q_lamQ k j →
      (b65q_P0invQ k * b65e_basisJetQ k n) i j = if n.val = 0 ∧ i = j then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored inverse jets invert the stored eigenbasis jets. -/
theorem b65e_basisInvJet_mul : ∀ k : Fin 4, ∀ n : Fin 8,
    ∑ a ∈ Finset.range (n.val + 1),
      b65e_basisJetQ k (Fin.ofNat 8 a) * b65e_basisInvJetQ k (Fin.ofNat 8 (n.val - a)) =
    if n.val = 0 then 1 else 0 := by
  decide +kernel

end HodgeLean.Foundations.Program
