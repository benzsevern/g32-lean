import HodgeLean.Foundations.Program.BraidCertificateReplaySeed

namespace HodgeLean.Foundations.Program

theorem b65b_qWord_two_cons (a b : b65s_Move) (w : List b65s_Move)
    (t : Fin 13 → (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ) :
    b65b_qWord (a :: b :: w) t = b65b_qWord w (b65b_qWord [a,b] t) := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_replay_calculation : b65b_qWord b65b_word b65b_qColumnRoot =
    b65b_replayStage43 := by
  rw [b65b_replay_seed]
  unfold b65b_word
  rw [b65b_qWord_two_cons, b65b_replayChunk0]
  rw [b65b_qWord_two_cons, b65b_replayChunk1]
  rw [b65b_qWord_two_cons, b65b_replayChunk2]
  rw [b65b_qWord_two_cons, b65b_replayChunk3]
  rw [b65b_qWord_two_cons, b65b_replayChunk4]
  rw [b65b_qWord_two_cons, b65b_replayChunk5]
  rw [b65b_qWord_two_cons, b65b_replayChunk6]
  rw [b65b_qWord_two_cons, b65b_replayChunk7]
  rw [b65b_qWord_two_cons, b65b_replayChunk8]
  rw [b65b_qWord_two_cons, b65b_replayChunk9]
  rw [b65b_qWord_two_cons, b65b_replayChunk10]
  rw [b65b_qWord_two_cons, b65b_replayChunk11]
  rw [b65b_qWord_two_cons, b65b_replayChunk12]
  rw [b65b_qWord_two_cons, b65b_replayChunk13]
  rw [b65b_qWord_two_cons, b65b_replayChunk14]
  rw [b65b_qWord_two_cons, b65b_replayChunk15]
  rw [b65b_qWord_two_cons, b65b_replayChunk16]
  rw [b65b_qWord_two_cons, b65b_replayChunk17]
  rw [b65b_qWord_two_cons, b65b_replayChunk18]
  rw [b65b_qWord_two_cons, b65b_replayChunk19]
  rw [b65b_qWord_two_cons, b65b_replayChunk20]
  rw [b65b_qWord_two_cons, b65b_replayChunk21]
  rw [b65b_qWord_two_cons, b65b_replayChunk22]
  rw [b65b_qWord_two_cons, b65b_replayChunk23]
  rw [b65b_qWord_two_cons, b65b_replayChunk24]
  rw [b65b_qWord_two_cons, b65b_replayChunk25]
  rw [b65b_qWord_two_cons, b65b_replayChunk26]
  rw [b65b_qWord_two_cons, b65b_replayChunk27]
  rw [b65b_qWord_two_cons, b65b_replayChunk28]
  rw [b65b_qWord_two_cons, b65b_replayChunk29]
  rw [b65b_qWord_two_cons, b65b_replayChunk30]
  rw [b65b_qWord_two_cons, b65b_replayChunk31]
  rw [b65b_qWord_two_cons, b65b_replayChunk32]
  rw [b65b_qWord_two_cons, b65b_replayChunk33]
  rw [b65b_qWord_two_cons, b65b_replayChunk34]
  rw [b65b_qWord_two_cons, b65b_replayChunk35]
  rw [b65b_qWord_two_cons, b65b_replayChunk36]
  rw [b65b_qWord_two_cons, b65b_replayChunk37]
  rw [b65b_qWord_two_cons, b65b_replayChunk38]
  rw [b65b_qWord_two_cons, b65b_replayChunk39]
  rw [b65b_qWord_two_cons, b65b_replayChunk40]
  rw [b65b_qWord_two_cons, b65b_replayChunk41]
  exact b65b_replayChunk42

end HodgeLean.Foundations.Program
