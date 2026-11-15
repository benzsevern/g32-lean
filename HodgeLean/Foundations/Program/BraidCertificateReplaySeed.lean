import HodgeLean.Foundations.Program.BraidCertificateReplayChecks

namespace HodgeLean.Foundations.Program

def b65b_qReflection (w : List (Fin 4)) : (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ :=
  let h := (w.map b65b_qGenerators).prod
  h * b65b_qGenerators 0 * h⁻¹

def b65b_qRoot : Fin 13 → (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ :=
  ![b65b_qGenerators 0, (b65b_qGenerators 0)⁻¹,
    (b65b_qGenerators 1)⁻¹, b65b_qGenerators 1,
    b65b_qReflection [2], (b65b_qReflection [2])⁻¹,
    b65b_qReflection [3], (b65b_qReflection [3])⁻¹,
    b65b_qReflection [1, 3, 1], (b65b_qReflection [0, 0, 2])⁻¹,
    b65b_qReflection [3, 2], (b65b_qReflection [3, 2, 1])⁻¹,
    (b65b_qGenerators 2)^2]

def b65b_qColumnRoot : Fin 13 → (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ :=
  fun i ↦ (b65b_qRoot i.rev)⁻¹

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replay_seed : b65b_qColumnRoot = b65b_replayStage0 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replay_endpoint (i : Fin 13) :
    (b65b_replayStage43 i).val = (b65b_qGenerators 1).inv *
      b65b_qDecode (b65b_finalIntegral i) * (b65b_qGenerators 1).val := by
  fin_cases i <;> decide +kernel


end HodgeLean.Foundations.Program
