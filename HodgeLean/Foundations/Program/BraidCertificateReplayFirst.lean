import HodgeLean.Foundations.Program.BraidCertificateReplayData

namespace HodgeLean.Foundations.Program

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk0 :
    b65b_qWord [.negative 4, .negative 5] b65b_replayStage0 = b65b_replayStage1 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk1 :
    b65b_qWord [.negative 3, .negative 4] b65b_replayStage1 = b65b_replayStage2 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk2 :
    b65b_qWord [.positive 2, .positive 3] b65b_replayStage2 = b65b_replayStage3 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk3 :
    b65b_qWord [.positive 3, .positive 2] b65b_replayStage3 = b65b_replayStage4 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk4 :
    b65b_qWord [.positive 4, .positive 3] b65b_replayStage4 = b65b_replayStage5 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk5 :
    b65b_qWord [.positive 5, .positive 4] b65b_replayStage5 = b65b_replayStage6 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk6 :
    b65b_qWord [.positive 6, .positive 5] b65b_replayStage6 = b65b_replayStage7 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk7 :
    b65b_qWord [.positive 5, .positive 6] b65b_replayStage7 = b65b_replayStage8 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk8 :
    b65b_qWord [.negative 4, .negative 5] b65b_replayStage8 = b65b_replayStage9 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk9 :
    b65b_qWord [.negative 3, .negative 4] b65b_replayStage9 = b65b_replayStage10 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk10 :
    b65b_qWord [.negative 2, .negative 3] b65b_replayStage10 = b65b_replayStage11 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk11 :
    b65b_qWord [.negative 1, .negative 2] b65b_replayStage11 = b65b_replayStage12 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk12 :
    b65b_qWord [.negative 2, .negative 1] b65b_replayStage12 = b65b_replayStage13 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk13 :
    b65b_qWord [.positive 3, .positive 2] b65b_replayStage13 = b65b_replayStage14 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk14 :
    b65b_qWord [.positive 4, .positive 3] b65b_replayStage14 = b65b_replayStage15 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk15 :
    b65b_qWord [.positive 5, .positive 4] b65b_replayStage15 = b65b_replayStage16 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk16 :
    b65b_qWord [.negative 5, .positive 2] b65b_replayStage16 = b65b_replayStage17 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk17 :
    b65b_qWord [.positive 3, .negative 2] b65b_replayStage17 = b65b_replayStage18 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk18 :
    b65b_qWord [.positive 1, .negative 4] b65b_replayStage18 = b65b_replayStage19 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk19 :
    b65b_qWord [.negative 5, .negative 3] b65b_replayStage19 = b65b_replayStage20 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk20 :
    b65b_qWord [.negative 3, .negative 2] b65b_replayStage20 = b65b_replayStage21 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replayChunk21 :
    b65b_qWord [.negative 1, .negative 1] b65b_replayStage21 = b65b_replayStage22 := by
  funext i
  apply Units.ext
  fin_cases i <;> decide +kernel


end HodgeLean.Foundations.Program
