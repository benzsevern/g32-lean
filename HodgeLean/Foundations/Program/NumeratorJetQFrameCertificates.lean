import HodgeLean.Foundations.Program.NumeratorJetQSystemDefs
import HodgeLean.Foundations.Program.KernelFramesCert

/-! # Rational kernel checks for the q-frame jets -/

namespace HodgeLean.Foundations.Program
open Matrix

set_option maxHeartbeats 400000 in
/-- The free rows of the stored q-frame jets. -/
theorem b65e_qFrameJet_free : ∀ n : Fin 8, ∀ a f : Fin 3,
    b65e_qFrameJet n (b65k_qFree a) f = if n.val = 0 ∧ a = f then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The rational block inverse inverts the order-zero selected q-pivot block. -/
theorem b65e_qBlockInv_mul : b65k_qBlockInv *
    (b65e_qSystemJetQ 0).submatrix b65k_qRows b65k_qPivot = 1 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 0. -/
theorem b65e_qFrameJet_kernel_0 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 0 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 1. -/
theorem b65e_qFrameJet_kernel_1 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 1 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 2. -/
theorem b65e_qFrameJet_kernel_2 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 2 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 3. -/
theorem b65e_qFrameJet_kernel_3 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 3 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 4. -/
theorem b65e_qFrameJet_kernel_4 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 4 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 5. -/
theorem b65e_qFrameJet_kernel_5 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 5 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 6. -/
theorem b65e_qFrameJet_kernel_6 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 6 = 0 := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The selected q-system rows annihilate the stored q-frame jets at order 7. -/
theorem b65e_qFrameJet_kernel_7 :
    b65e_convQ (fun a ↦ (b65e_qSystemJetQ a).submatrix b65k_qRows id) b65e_qFrameN 7 = 0 := by
  decide +kernel

end HodgeLean.Foundations.Program
