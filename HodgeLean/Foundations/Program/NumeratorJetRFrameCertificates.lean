import HodgeLean.Foundations.Program.NumeratorJetRSystemEvaluation

/-! # Rational kernel checks for the r-frame jets -/

namespace HodgeLean.Foundations.Program
open Matrix

/-- Natural-indexed stored r-frame jets. -/
def b65e_rFrameN (a : ℕ) : Matrix (Fin 36) (Fin 3) ℚ := b65e_rFrameJet (Fin.ofNat 8 a)

set_option maxHeartbeats 400000 in
/-- The free rows of the stored r-frame jets. -/
theorem b65e_rFrameJet_free : ∀ n : Fin 8, ∀ a f : Fin 3,
    b65e_rFrameJet n (b65k_rFree a) f = if n.val = 0 ∧ a = f then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 0. -/
theorem b65e_rFrameJet_kernel_0 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 0 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 1. -/
theorem b65e_rFrameJet_kernel_1 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 1 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 2. -/
theorem b65e_rFrameJet_kernel_2 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 2 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 3. -/
theorem b65e_rFrameJet_kernel_3 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 3 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 4. -/
theorem b65e_rFrameJet_kernel_4 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 4 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 5. -/
theorem b65e_rFrameJet_kernel_5 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 5 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 6. -/
theorem b65e_rFrameJet_kernel_6 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 6 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected r-system rows annihilate the stored r-frame jets at order 7. -/
theorem b65e_rFrameJet_kernel_7 :
    b65e_convQ (fun a ↦ (b65e_rSystemJetQ a).submatrix b65k_rRows id) b65e_rFrameN 7 = 0 := by
  decide +kernel

end HodgeLean.Foundations.Program
