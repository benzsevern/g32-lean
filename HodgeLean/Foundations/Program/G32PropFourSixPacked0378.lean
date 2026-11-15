import HodgeLean.Foundations.Program.G32PropFourSixPacked0376
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0377

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_038_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 0 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 9 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 0 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 9 9, g32p_row19_traceSegment_038_0000_0009, g32p_row19_traceSegment_038_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 18 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 27 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 18 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 18 9 9, g32p_row19_traceSegment_038_0018_0009, g32p_row19_traceSegment_038_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 0 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 18 18, g32p_row19_traceSegment_038_0000_0018, g32p_row19_traceSegment_038_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 36 9 9, g32p_row19_traceSegment_038_0036_0009, g32p_row19_traceSegment_038_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 54 9 9, g32p_row19_traceSegment_038_0054_0009, g32p_row19_traceSegment_038_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 36 18 18, g32p_row19_traceSegment_038_0036_0018, g32p_row19_traceSegment_038_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 0 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 36 36, g32p_row19_traceSegment_038_0000_0036, g32p_row19_traceSegment_038_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 72 9 9, g32p_row19_traceSegment_038_0072_0009, g32p_row19_traceSegment_038_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 90 9 9, g32p_row19_traceSegment_038_0090_0009, g32p_row19_traceSegment_038_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 72 18 18, g32p_row19_traceSegment_038_0072_0018, g32p_row19_traceSegment_038_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 108 9 9, g32p_row19_traceSegment_038_0108_0009, g32p_row19_traceSegment_038_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 126 9 9, g32p_row19_traceSegment_038_0126_0009, g32p_row19_traceSegment_038_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 108 18 18, g32p_row19_traceSegment_038_0108_0018, g32p_row19_traceSegment_038_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 72 36 36, g32p_row19_traceSegment_038_0072_0036, g32p_row19_traceSegment_038_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 0 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 72 72, g32p_row19_traceSegment_038_0000_0072, g32p_row19_traceSegment_038_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 144 9 9, g32p_row19_traceSegment_038_0144_0009, g32p_row19_traceSegment_038_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 171 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 162 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 162 9 9, g32p_row19_traceSegment_038_0162_0009, g32p_row19_traceSegment_038_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 144 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 144 18 18, g32p_row19_traceSegment_038_0144_0018, g32p_row19_traceSegment_038_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 180 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 189 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 180 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 180 9 9, g32p_row19_traceSegment_038_0180_0009, g32p_row19_traceSegment_038_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 198 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 198 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 198 9 9, g32p_row19_traceSegment_038_0198_0009, g32p_row19_traceSegment_038_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 180 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 180 18 18, g32p_row19_traceSegment_038_0180_0018, g32p_row19_traceSegment_038_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 144 72 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 144 36 36, g32p_row19_traceSegment_038_0144_0036, g32p_row19_traceSegment_038_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 216 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 216 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 216 9 9, g32p_row19_traceSegment_038_0216_0009, g32p_row19_traceSegment_038_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 234 9 9, g32p_row19_traceSegment_038_0234_0009, g32p_row19_traceSegment_038_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 216 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 216 18 18, g32p_row19_traceSegment_038_0216_0018, g32p_row19_traceSegment_038_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 252 9 9, g32p_row19_traceSegment_038_0252_0009, g32p_row19_traceSegment_038_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 270 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 270 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 270 9 9, g32p_row19_traceSegment_038_0270_0009, g32p_row19_traceSegment_038_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 252 18 18, g32p_row19_traceSegment_038_0252_0018, g32p_row19_traceSegment_038_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 216 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 216 36 36, g32p_row19_traceSegment_038_0216_0036, g32p_row19_traceSegment_038_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 144 144 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 144 72 72, g32p_row19_traceSegment_038_0144_0072, g32p_row19_traceSegment_038_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_038 0 288 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 144 144, g32p_row19_traceSegment_038_0000_0144, g32p_row19_traceSegment_038_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 288 9 9, g32p_row19_traceSegment_038_0288_0009, g32p_row19_traceSegment_038_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 315 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 306 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 306 9 9, g32p_row19_traceSegment_038_0306_0009, g32p_row19_traceSegment_038_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 288 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 288 18 18, g32p_row19_traceSegment_038_0288_0018, g32p_row19_traceSegment_038_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 324 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 333 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 324 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 324 9 9, g32p_row19_traceSegment_038_0324_0009, g32p_row19_traceSegment_038_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 342 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 342 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 342 9 9, g32p_row19_traceSegment_038_0342_0009, g32p_row19_traceSegment_038_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 324 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 324 18 18, g32p_row19_traceSegment_038_0324_0018, g32p_row19_traceSegment_038_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 288 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 288 36 36, g32p_row19_traceSegment_038_0288_0036, g32p_row19_traceSegment_038_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 360 9 9, g32p_row19_traceSegment_038_0360_0009, g32p_row19_traceSegment_038_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 378 9 9, g32p_row19_traceSegment_038_0378_0009, g32p_row19_traceSegment_038_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 360 18 18, g32p_row19_traceSegment_038_0360_0018, g32p_row19_traceSegment_038_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 396 9 9, g32p_row19_traceSegment_038_0396_0009, g32p_row19_traceSegment_038_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 414 9 9, g32p_row19_traceSegment_038_0414_0009, g32p_row19_traceSegment_038_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 396 18 18, g32p_row19_traceSegment_038_0396_0018, g32p_row19_traceSegment_038_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 360 36 36, g32p_row19_traceSegment_038_0360_0036, g32p_row19_traceSegment_038_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 288 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 288 72 72, g32p_row19_traceSegment_038_0288_0072, g32p_row19_traceSegment_038_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 432 9 9, g32p_row19_traceSegment_038_0432_0009, g32p_row19_traceSegment_038_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 450 9 9, g32p_row19_traceSegment_038_0450_0009, g32p_row19_traceSegment_038_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 432 18 18, g32p_row19_traceSegment_038_0432_0018, g32p_row19_traceSegment_038_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 468 9 9, g32p_row19_traceSegment_038_0468_0009, g32p_row19_traceSegment_038_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 486 9 9, g32p_row19_traceSegment_038_0486_0009, g32p_row19_traceSegment_038_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 468 18 18, g32p_row19_traceSegment_038_0468_0018, g32p_row19_traceSegment_038_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 432 36 36, g32p_row19_traceSegment_038_0432_0036, g32p_row19_traceSegment_038_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 504 9 9, g32p_row19_traceSegment_038_0504_0009, g32p_row19_traceSegment_038_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 522 9 9, g32p_row19_traceSegment_038_0522_0009, g32p_row19_traceSegment_038_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 504 18 18, g32p_row19_traceSegment_038_0504_0018, g32p_row19_traceSegment_038_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 540 9 9, g32p_row19_traceSegment_038_0540_0009, g32p_row19_traceSegment_038_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 558 9 9, g32p_row19_traceSegment_038_0558_0009, g32p_row19_traceSegment_038_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 540 18 18, g32p_row19_traceSegment_038_0540_0018, g32p_row19_traceSegment_038_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 504 36 36, g32p_row19_traceSegment_038_0504_0036, g32p_row19_traceSegment_038_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 432 72 72, g32p_row19_traceSegment_038_0432_0072, g32p_row19_traceSegment_038_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_038 288 288 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 288 144 144, g32p_row19_traceSegment_038_0288_0144, g32p_row19_traceSegment_038_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_038 0 576 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 288 288, g32p_row19_traceSegment_038_0000_0288, g32p_row19_traceSegment_038_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 585 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 576 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 576 9 9, g32p_row19_traceSegment_038_0576_0009, g32p_row19_traceSegment_038_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 594 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 603 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 594 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 594 9 9, g32p_row19_traceSegment_038_0594_0009, g32p_row19_traceSegment_038_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 576 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 576 18 18, g32p_row19_traceSegment_038_0576_0018, g32p_row19_traceSegment_038_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 612 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 621 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 612 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 612 9 9, g32p_row19_traceSegment_038_0612_0009, g32p_row19_traceSegment_038_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 630 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 639 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 630 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 630 9 9, g32p_row19_traceSegment_038_0630_0009, g32p_row19_traceSegment_038_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 612 36 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 612 18 18, g32p_row19_traceSegment_038_0612_0018, g32p_row19_traceSegment_038_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 576 72 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 576 36 36, g32p_row19_traceSegment_038_0576_0036, g32p_row19_traceSegment_038_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 648 9 9, g32p_row19_traceSegment_038_0648_0009, g32p_row19_traceSegment_038_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 666 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 666 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 666 9 9, g32p_row19_traceSegment_038_0666_0009, g32p_row19_traceSegment_038_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 648 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 648 18 18, g32p_row19_traceSegment_038_0648_0018, g32p_row19_traceSegment_038_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 684 9 9, g32p_row19_traceSegment_038_0684_0009, g32p_row19_traceSegment_038_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 702 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 711 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 702 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 702 9 9, g32p_row19_traceSegment_038_0702_0009, g32p_row19_traceSegment_038_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 684 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 684 18 18, g32p_row19_traceSegment_038_0684_0018, g32p_row19_traceSegment_038_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 648 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 648 36 36, g32p_row19_traceSegment_038_0648_0036, g32p_row19_traceSegment_038_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 576 144 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 576 72 72, g32p_row19_traceSegment_038_0576_0072, g32p_row19_traceSegment_038_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 720 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 729 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 720 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 720 9 9, g32p_row19_traceSegment_038_0720_0009, g32p_row19_traceSegment_038_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 747 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 738 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 738 9 9, g32p_row19_traceSegment_038_0738_0009, g32p_row19_traceSegment_038_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 720 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 720 18 18, g32p_row19_traceSegment_038_0720_0018, g32p_row19_traceSegment_038_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 756 9 9, g32p_row19_traceSegment_038_0756_0009, g32p_row19_traceSegment_038_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 774 9 9, g32p_row19_traceSegment_038_0774_0009, g32p_row19_traceSegment_038_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 756 18 18, g32p_row19_traceSegment_038_0756_0018, g32p_row19_traceSegment_038_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 720 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 720 36 36, g32p_row19_traceSegment_038_0720_0036, g32p_row19_traceSegment_038_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 792 9 9, g32p_row19_traceSegment_038_0792_0009, g32p_row19_traceSegment_038_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 819 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 810 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 810 9 9, g32p_row19_traceSegment_038_0810_0009, g32p_row19_traceSegment_038_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 792 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 792 18 18, g32p_row19_traceSegment_038_0792_0018, g32p_row19_traceSegment_038_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 837 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 828 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 828 9 9, g32p_row19_traceSegment_038_0828_0009, g32p_row19_traceSegment_038_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 846 9 9, g32p_row19_traceSegment_038_0846_0009, g32p_row19_traceSegment_038_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 828 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 828 18 18, g32p_row19_traceSegment_038_0828_0018, g32p_row19_traceSegment_038_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 792 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 792 36 36, g32p_row19_traceSegment_038_0792_0036, g32p_row19_traceSegment_038_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 720 144 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 720 72 72, g32p_row19_traceSegment_038_0720_0072, g32p_row19_traceSegment_038_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_038 576 288 = [0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 576 144 144, g32p_row19_traceSegment_038_0576_0144, g32p_row19_traceSegment_038_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 864 9 9, g32p_row19_traceSegment_038_0864_0009, g32p_row19_traceSegment_038_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 882 9 9, g32p_row19_traceSegment_038_0882_0009, g32p_row19_traceSegment_038_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 864 18 18, g32p_row19_traceSegment_038_0864_0018, g32p_row19_traceSegment_038_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 900 9 9, g32p_row19_traceSegment_038_0900_0009, g32p_row19_traceSegment_038_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 918 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 918 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 918 9 9, g32p_row19_traceSegment_038_0918_0009, g32p_row19_traceSegment_038_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 900 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 900 18 18, g32p_row19_traceSegment_038_0900_0018, g32p_row19_traceSegment_038_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 864 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 864 36 36, g32p_row19_traceSegment_038_0864_0036, g32p_row19_traceSegment_038_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 936 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 945 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 936 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 936 9 9, g32p_row19_traceSegment_038_0936_0009, g32p_row19_traceSegment_038_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 954 9 9, g32p_row19_traceSegment_038_0954_0009, g32p_row19_traceSegment_038_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 936 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 936 18 18, g32p_row19_traceSegment_038_0936_0018, g32p_row19_traceSegment_038_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 981 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 972 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 972 9 9, g32p_row19_traceSegment_038_0972_0009, g32p_row19_traceSegment_038_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 990 9 9, g32p_row19_traceSegment_038_0990_0009, g32p_row19_traceSegment_038_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 972 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 972 18 18, g32p_row19_traceSegment_038_0972_0018, g32p_row19_traceSegment_038_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 936 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 936 36 36, g32p_row19_traceSegment_038_0936_0036, g32p_row19_traceSegment_038_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 864 144 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 864 72 72, g32p_row19_traceSegment_038_0864_0072, g32p_row19_traceSegment_038_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1008 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1008 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1008 9 9, g32p_row19_traceSegment_038_1008_0009, g32p_row19_traceSegment_038_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1035 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1026 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1026 9 9, g32p_row19_traceSegment_038_1026_0009, g32p_row19_traceSegment_038_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 1008 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1008 18 18, g32p_row19_traceSegment_038_1008_0018, g32p_row19_traceSegment_038_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1044 9 9, g32p_row19_traceSegment_038_1044_0009, g32p_row19_traceSegment_038_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1062 9 9, g32p_row19_traceSegment_038_1062_0009, g32p_row19_traceSegment_038_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1044 18 18, g32p_row19_traceSegment_038_1044_0018, g32p_row19_traceSegment_038_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 1008 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1008 36 36, g32p_row19_traceSegment_038_1008_0036, g32p_row19_traceSegment_038_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1080 9 9, g32p_row19_traceSegment_038_1080_0009, g32p_row19_traceSegment_038_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1098 9 9, g32p_row19_traceSegment_038_1098_0009, g32p_row19_traceSegment_038_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1080 18 18, g32p_row19_traceSegment_038_1080_0018, g32p_row19_traceSegment_038_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1116 9 9, g32p_row19_traceSegment_038_1116_0009, g32p_row19_traceSegment_038_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1134 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_038 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_038_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_038 1134 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1134 9 9, g32p_row19_traceSegment_038_1134_0009, g32p_row19_traceSegment_038_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_038 1116 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1116 18 18, g32p_row19_traceSegment_038_1116_0018, g32p_row19_traceSegment_038_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_038 1080 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1080 36 36, g32p_row19_traceSegment_038_1080_0036, g32p_row19_traceSegment_038_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_038_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_038 1008 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 1008 72 72, g32p_row19_traceSegment_038_1008_0072, g32p_row19_traceSegment_038_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_038 864 288 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 864 144 144, g32p_row19_traceSegment_038_0864_0144, g32p_row19_traceSegment_038_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_038 576 576 = [0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 576 288 288, g32p_row19_traceSegment_038_0576_0288, g32p_row19_traceSegment_038_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_038_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_038 0 1152 = [0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_038 0 576 576, g32p_row19_traceSegment_038_0000_0576, g32p_row19_traceSegment_038_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 38 = [0, 0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_038_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_043 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 43 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_043_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 9 9, g32p_row19_traceSegment_043_0000_0009, g32p_row19_traceSegment_043_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 18 9 9, g32p_row19_traceSegment_043_0018_0009, g32p_row19_traceSegment_043_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 18 18, g32p_row19_traceSegment_043_0000_0018, g32p_row19_traceSegment_043_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 36 9 9, g32p_row19_traceSegment_043_0036_0009, g32p_row19_traceSegment_043_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 54 9 9, g32p_row19_traceSegment_043_0054_0009, g32p_row19_traceSegment_043_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 36 18 18, g32p_row19_traceSegment_043_0036_0018, g32p_row19_traceSegment_043_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 36 36, g32p_row19_traceSegment_043_0000_0036, g32p_row19_traceSegment_043_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 72 9 9, g32p_row19_traceSegment_043_0072_0009, g32p_row19_traceSegment_043_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 90 9 9, g32p_row19_traceSegment_043_0090_0009, g32p_row19_traceSegment_043_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 72 18 18, g32p_row19_traceSegment_043_0072_0018, g32p_row19_traceSegment_043_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 117 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 108 9 9, g32p_row19_traceSegment_043_0108_0009, g32p_row19_traceSegment_043_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 126 9 9, g32p_row19_traceSegment_043_0126_0009, g32p_row19_traceSegment_043_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 108 18 18, g32p_row19_traceSegment_043_0108_0018, g32p_row19_traceSegment_043_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 72 36 36, g32p_row19_traceSegment_043_0072_0036, g32p_row19_traceSegment_043_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 0 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 72 72, g32p_row19_traceSegment_043_0000_0072, g32p_row19_traceSegment_043_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 153 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 144 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 144 9 9, g32p_row19_traceSegment_043_0144_0009, g32p_row19_traceSegment_043_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 162 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 162 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 162 9 9, g32p_row19_traceSegment_043_0162_0009, g32p_row19_traceSegment_043_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 144 36 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 144 18 18, g32p_row19_traceSegment_043_0144_0018, g32p_row19_traceSegment_043_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 180 9 9, g32p_row19_traceSegment_043_0180_0009, g32p_row19_traceSegment_043_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 198 9 9, g32p_row19_traceSegment_043_0198_0009, g32p_row19_traceSegment_043_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 180 18 18, g32p_row19_traceSegment_043_0180_0018, g32p_row19_traceSegment_043_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 144 72 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 144 36 36, g32p_row19_traceSegment_043_0144_0036, g32p_row19_traceSegment_043_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 216 9 9, g32p_row19_traceSegment_043_0216_0009, g32p_row19_traceSegment_043_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 234 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 243 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 234 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 234 9 9, g32p_row19_traceSegment_043_0234_0009, g32p_row19_traceSegment_043_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 216 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 216 18 18, g32p_row19_traceSegment_043_0216_0018, g32p_row19_traceSegment_043_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 252 9 9, g32p_row19_traceSegment_043_0252_0009, g32p_row19_traceSegment_043_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 279 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 270 9 9, g32p_row19_traceSegment_043_0270_0009, g32p_row19_traceSegment_043_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 252 18 18, g32p_row19_traceSegment_043_0252_0018, g32p_row19_traceSegment_043_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 216 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 216 36 36, g32p_row19_traceSegment_043_0216_0036, g32p_row19_traceSegment_043_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 144 144 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 144 72 72, g32p_row19_traceSegment_043_0144_0072, g32p_row19_traceSegment_043_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_043 0 288 = [0, 1, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 144 144, g32p_row19_traceSegment_043_0000_0144, g32p_row19_traceSegment_043_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 288 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 297 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 288 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 288 9 9, g32p_row19_traceSegment_043_0288_0009, g32p_row19_traceSegment_043_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 306 9 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 306 18 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 306 9 9, g32p_row19_traceSegment_043_0306_0009, g32p_row19_traceSegment_043_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 288 36 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 288 18 18, g32p_row19_traceSegment_043_0288_0018, g32p_row19_traceSegment_043_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 324 9 9, g32p_row19_traceSegment_043_0324_0009, g32p_row19_traceSegment_043_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 342 9 9, g32p_row19_traceSegment_043_0342_0009, g32p_row19_traceSegment_043_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 324 18 18, g32p_row19_traceSegment_043_0324_0018, g32p_row19_traceSegment_043_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 288 72 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 288 36 36, g32p_row19_traceSegment_043_0288_0036, g32p_row19_traceSegment_043_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 360 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 369 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 360 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 360 9 9, g32p_row19_traceSegment_043_0360_0009, g32p_row19_traceSegment_043_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 378 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 387 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 378 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 378 9 9, g32p_row19_traceSegment_043_0378_0009, g32p_row19_traceSegment_043_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 360 36 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 360 18 18, g32p_row19_traceSegment_043_0360_0018, g32p_row19_traceSegment_043_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 396 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 396 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 396 9 9, g32p_row19_traceSegment_043_0396_0009, g32p_row19_traceSegment_043_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 414 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 423 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 414 18 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 414 9 9, g32p_row19_traceSegment_043_0414_0009, g32p_row19_traceSegment_043_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 396 36 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 396 18 18, g32p_row19_traceSegment_043_0396_0018, g32p_row19_traceSegment_043_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 360 72 = [0, 10, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 360 36 36, g32p_row19_traceSegment_043_0360_0036, g32p_row19_traceSegment_043_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 288 144 = [0, 11, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 288 72 72, g32p_row19_traceSegment_043_0288_0072, g32p_row19_traceSegment_043_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 432 9 9, g32p_row19_traceSegment_043_0432_0009, g32p_row19_traceSegment_043_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 450 9 9, g32p_row19_traceSegment_043_0450_0009, g32p_row19_traceSegment_043_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 432 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 432 18 18, g32p_row19_traceSegment_043_0432_0018, g32p_row19_traceSegment_043_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 468 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 477 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 468 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 468 9 9, g32p_row19_traceSegment_043_0468_0009, g32p_row19_traceSegment_043_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 486 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 486 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 486 9 9, g32p_row19_traceSegment_043_0486_0009, g32p_row19_traceSegment_043_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 468 36 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 468 18 18, g32p_row19_traceSegment_043_0468_0018, g32p_row19_traceSegment_043_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 432 72 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 432 36 36, g32p_row19_traceSegment_043_0432_0036, g32p_row19_traceSegment_043_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 504 9 9, g32p_row19_traceSegment_043_0504_0009, g32p_row19_traceSegment_043_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 522 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 522 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 522 9 9, g32p_row19_traceSegment_043_0522_0009, g32p_row19_traceSegment_043_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 504 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 504 18 18, g32p_row19_traceSegment_043_0504_0018, g32p_row19_traceSegment_043_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 549 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 540 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 540 9 9, g32p_row19_traceSegment_043_0540_0009, g32p_row19_traceSegment_043_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 558 9 9, g32p_row19_traceSegment_043_0558_0009, g32p_row19_traceSegment_043_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 540 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 540 18 18, g32p_row19_traceSegment_043_0540_0018, g32p_row19_traceSegment_043_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 504 72 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 504 36 36, g32p_row19_traceSegment_043_0504_0036, g32p_row19_traceSegment_043_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 432 144 = [0, 4, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 432 72 72, g32p_row19_traceSegment_043_0432_0072, g32p_row19_traceSegment_043_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_043 288 288 = [0, 15, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 288 144 144, g32p_row19_traceSegment_043_0288_0144, g32p_row19_traceSegment_043_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_043 0 576 = [0, 16, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 288 288, g32p_row19_traceSegment_043_0000_0288, g32p_row19_traceSegment_043_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 576 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 585 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 576 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 576 9 9, g32p_row19_traceSegment_043_0576_0009, g32p_row19_traceSegment_043_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 603 9 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 594 18 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 594 9 9, g32p_row19_traceSegment_043_0594_0009, g32p_row19_traceSegment_043_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 576 36 = [0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 576 18 18, g32p_row19_traceSegment_043_0576_0018, g32p_row19_traceSegment_043_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 612 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 612 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 612 9 9, g32p_row19_traceSegment_043_0612_0009, g32p_row19_traceSegment_043_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 630 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 639 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 630 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 630 9 9, g32p_row19_traceSegment_043_0630_0009, g32p_row19_traceSegment_043_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 612 36 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 612 18 18, g32p_row19_traceSegment_043_0612_0018, g32p_row19_traceSegment_043_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 576 72 = [0, 2, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 576 36 36, g32p_row19_traceSegment_043_0576_0036, g32p_row19_traceSegment_043_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 657 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 648 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 648 9 9, g32p_row19_traceSegment_043_0648_0009, g32p_row19_traceSegment_043_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 675 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 666 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 666 9 9, g32p_row19_traceSegment_043_0666_0009, g32p_row19_traceSegment_043_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 648 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 648 18 18, g32p_row19_traceSegment_043_0648_0018, g32p_row19_traceSegment_043_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 684 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 684 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 684 9 9, g32p_row19_traceSegment_043_0684_0009, g32p_row19_traceSegment_043_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 702 9 9, g32p_row19_traceSegment_043_0702_0009, g32p_row19_traceSegment_043_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 684 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 684 18 18, g32p_row19_traceSegment_043_0684_0018, g32p_row19_traceSegment_043_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 648 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 648 36 36, g32p_row19_traceSegment_043_0648_0036, g32p_row19_traceSegment_043_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 576 144 = [0, 5, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 576 72 72, g32p_row19_traceSegment_043_0576_0072, g32p_row19_traceSegment_043_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 729 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 720 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 720 9 9, g32p_row19_traceSegment_043_0720_0009, g32p_row19_traceSegment_043_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 738 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 738 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 738 9 9, g32p_row19_traceSegment_043_0738_0009, g32p_row19_traceSegment_043_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 720 36 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 720 18 18, g32p_row19_traceSegment_043_0720_0018, g32p_row19_traceSegment_043_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 765 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 756 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 756 9 9, g32p_row19_traceSegment_043_0756_0009, g32p_row19_traceSegment_043_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 774 9 9, g32p_row19_traceSegment_043_0774_0009, g32p_row19_traceSegment_043_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 756 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 756 18 18, g32p_row19_traceSegment_043_0756_0018, g32p_row19_traceSegment_043_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 720 72 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 720 36 36, g32p_row19_traceSegment_043_0720_0036, g32p_row19_traceSegment_043_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 792 9 9, g32p_row19_traceSegment_043_0792_0009, g32p_row19_traceSegment_043_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 810 9 9, g32p_row19_traceSegment_043_0810_0009, g32p_row19_traceSegment_043_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 792 18 18, g32p_row19_traceSegment_043_0792_0018, g32p_row19_traceSegment_043_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 828 9 9, g32p_row19_traceSegment_043_0828_0009, g32p_row19_traceSegment_043_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 846 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 855 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 846 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 846 9 9, g32p_row19_traceSegment_043_0846_0009, g32p_row19_traceSegment_043_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 828 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 828 18 18, g32p_row19_traceSegment_043_0828_0018, g32p_row19_traceSegment_043_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 792 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 792 36 36, g32p_row19_traceSegment_043_0792_0036, g32p_row19_traceSegment_043_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 720 144 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 720 72 72, g32p_row19_traceSegment_043_0720_0072, g32p_row19_traceSegment_043_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_043 576 288 = [0, 8, 10] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 576 144 144, g32p_row19_traceSegment_043_0576_0144, g32p_row19_traceSegment_043_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 864 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 873 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 864 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 864 9 9, g32p_row19_traceSegment_043_0864_0009, g32p_row19_traceSegment_043_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 891 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 882 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 882 9 9, g32p_row19_traceSegment_043_0882_0009, g32p_row19_traceSegment_043_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 864 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 864 18 18, g32p_row19_traceSegment_043_0864_0018, g32p_row19_traceSegment_043_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 900 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 909 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 900 18 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 900 9 9, g32p_row19_traceSegment_043_0900_0009, g32p_row19_traceSegment_043_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 927 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 918 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 918 9 9, g32p_row19_traceSegment_043_0918_0009, g32p_row19_traceSegment_043_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 900 36 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 900 18 18, g32p_row19_traceSegment_043_0900_0018, g32p_row19_traceSegment_043_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 864 72 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 864 36 36, g32p_row19_traceSegment_043_0864_0036, g32p_row19_traceSegment_043_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 945 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 936 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 936 9 9, g32p_row19_traceSegment_043_0936_0009, g32p_row19_traceSegment_043_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 954 9 9, g32p_row19_traceSegment_043_0954_0009, g32p_row19_traceSegment_043_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 936 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 936 18 18, g32p_row19_traceSegment_043_0936_0018, g32p_row19_traceSegment_043_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 981 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 972 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 972 9 9, g32p_row19_traceSegment_043_0972_0009, g32p_row19_traceSegment_043_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 990 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 990 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 990 9 9, g32p_row19_traceSegment_043_0990_0009, g32p_row19_traceSegment_043_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 972 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 972 18 18, g32p_row19_traceSegment_043_0972_0018, g32p_row19_traceSegment_043_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 936 72 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 936 36 36, g32p_row19_traceSegment_043_0936_0036, g32p_row19_traceSegment_043_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 864 144 = [0, 3, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 864 72 72, g32p_row19_traceSegment_043_0864_0072, g32p_row19_traceSegment_043_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1008 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1008 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1008 9 9, g32p_row19_traceSegment_043_1008_0009, g32p_row19_traceSegment_043_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1026 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1026 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1026 9 9, g32p_row19_traceSegment_043_1026_0009, g32p_row19_traceSegment_043_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 1008 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1008 18 18, g32p_row19_traceSegment_043_1008_0018, g32p_row19_traceSegment_043_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1044 9 9, g32p_row19_traceSegment_043_1044_0009, g32p_row19_traceSegment_043_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1062 9 9, g32p_row19_traceSegment_043_1062_0009, g32p_row19_traceSegment_043_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1044 18 18, g32p_row19_traceSegment_043_1044_0018, g32p_row19_traceSegment_043_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 1008 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1008 36 36, g32p_row19_traceSegment_043_1008_0036, g32p_row19_traceSegment_043_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1089 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1080 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1080 9 9, g32p_row19_traceSegment_043_1080_0009, g32p_row19_traceSegment_043_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1098 9 9, g32p_row19_traceSegment_043_1098_0009, g32p_row19_traceSegment_043_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 1080 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1080 18 18, g32p_row19_traceSegment_043_1080_0018, g32p_row19_traceSegment_043_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1125 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1116 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1116 9 9, g32p_row19_traceSegment_043_1116_0009, g32p_row19_traceSegment_043_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_043 1143 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_043_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_043 1134 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1134 9 9, g32p_row19_traceSegment_043_1134_0009, g32p_row19_traceSegment_043_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_043 1116 36 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1116 18 18, g32p_row19_traceSegment_043_1116_0018, g32p_row19_traceSegment_043_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_043 1080 72 = [0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1080 36 36, g32p_row19_traceSegment_043_1080_0036, g32p_row19_traceSegment_043_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_043_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_043 1008 144 = [0, 5, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 1008 72 72, g32p_row19_traceSegment_043_1008_0072, g32p_row19_traceSegment_043_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_043 864 288 = [0, 8, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 864 144 144, g32p_row19_traceSegment_043_0864_0144, g32p_row19_traceSegment_043_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_043 576 576 = [0, 16, 18] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 576 288 288, g32p_row19_traceSegment_043_0576_0288, g32p_row19_traceSegment_043_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_043_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_043 0 1152 = [0, 32, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_043 0 576 576, g32p_row19_traceSegment_043_0000_0576, g32p_row19_traceSegment_043_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 43 = [0, 32, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_043_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row19_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 25) (g32p_literalTraceValue 18 25)
      [1, -1, 1] [-3456] = true := by
  rw [g32p_row19_traceCoefficients_025]
  decide +kernel

theorem g32p_row19_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 29) (g32p_literalTraceValue 18 29)
      [1, -1, 1] [0, 0, 3456, 3456] = true := by
  rw [g32p_row19_traceCoefficients_029]
  decide +kernel

theorem g32p_row19_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 30) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 30) (g32p_literalTraceValue 18 30)
      [1, -1, 1] [1152, 1152, 1152, 1152] = true := by
  rw [g32p_row19_traceCoefficients_030]
  decide +kernel

theorem g32p_row19_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 31) (g32p_literalTraceValue 18 31)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row19_traceCoefficients_031]
  decide +kernel

theorem g32p_row19_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 34) (g32p_literalTraceValue 18 34)
      [1, -1, 1] [8064, 10368, 10368] = true := by
  rw [g32p_row19_traceCoefficients_034]
  decide +kernel

theorem g32p_row19_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 37) (g32p_literalTraceValue 18 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row19_traceCoefficients_037]
  decide +kernel

theorem g32p_row19_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 38) (g32p_literalTraceValue 18 38)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row19_traceCoefficients_038]
  decide +kernel

theorem g32p_row19_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 43) (g32p_literalTraceValue 18 43)
      [1, -1, 1] [-3456] = true := by
  rw [g32p_row19_traceCoefficients_043]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_046_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 9 9, g32p_row19_traceSegment_046_0000_0009, g32p_row19_traceSegment_046_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 18 9 9, g32p_row19_traceSegment_046_0018_0009, g32p_row19_traceSegment_046_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 18 18, g32p_row19_traceSegment_046_0000_0018, g32p_row19_traceSegment_046_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 45 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 36 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 36 9 9, g32p_row19_traceSegment_046_0036_0009, g32p_row19_traceSegment_046_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 54 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 63 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 54 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 54 9 9, g32p_row19_traceSegment_046_0054_0009, g32p_row19_traceSegment_046_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 36 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 36 18 18, g32p_row19_traceSegment_046_0036_0018, g32p_row19_traceSegment_046_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 0 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 36 36, g32p_row19_traceSegment_046_0000_0036, g32p_row19_traceSegment_046_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 72 9 9, g32p_row19_traceSegment_046_0072_0009, g32p_row19_traceSegment_046_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 99 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 90 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 90 9 9, g32p_row19_traceSegment_046_0090_0009, g32p_row19_traceSegment_046_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 72 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 72 18 18, g32p_row19_traceSegment_046_0072_0018, g32p_row19_traceSegment_046_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 108 9 9, g32p_row19_traceSegment_046_0108_0009, g32p_row19_traceSegment_046_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 126 9 = [0, 1, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 126 18 = [0, 1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 126 9 9, g32p_row19_traceSegment_046_0126_0009, g32p_row19_traceSegment_046_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 108 36 = [0, 1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 108 18 18, g32p_row19_traceSegment_046_0108_0018, g32p_row19_traceSegment_046_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 72 72 = [0, 1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 72 36 36, g32p_row19_traceSegment_046_0072_0036, g32p_row19_traceSegment_046_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 0 144 = [0, 4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 72 72, g32p_row19_traceSegment_046_0000_0072, g32p_row19_traceSegment_046_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 144 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 153 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 144 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 144 9 9, g32p_row19_traceSegment_046_0144_0009, g32p_row19_traceSegment_046_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 171 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 162 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 162 9 9, g32p_row19_traceSegment_046_0162_0009, g32p_row19_traceSegment_046_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 144 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 144 18 18, g32p_row19_traceSegment_046_0144_0018, g32p_row19_traceSegment_046_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 180 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 180 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 180 9 9, g32p_row19_traceSegment_046_0180_0009, g32p_row19_traceSegment_046_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 198 9 9, g32p_row19_traceSegment_046_0198_0009, g32p_row19_traceSegment_046_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 180 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 180 18 18, g32p_row19_traceSegment_046_0180_0018, g32p_row19_traceSegment_046_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 144 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 144 36 36, g32p_row19_traceSegment_046_0144_0036, g32p_row19_traceSegment_046_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 216 9 9, g32p_row19_traceSegment_046_0216_0009, g32p_row19_traceSegment_046_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 234 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 234 9 9, g32p_row19_traceSegment_046_0234_0009, g32p_row19_traceSegment_046_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 216 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 216 18 18, g32p_row19_traceSegment_046_0216_0018, g32p_row19_traceSegment_046_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 252 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 261 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 252 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 252 9 9, g32p_row19_traceSegment_046_0252_0009, g32p_row19_traceSegment_046_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 279 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 270 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 270 9 9, g32p_row19_traceSegment_046_0270_0009, g32p_row19_traceSegment_046_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 252 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 252 18 18, g32p_row19_traceSegment_046_0252_0018, g32p_row19_traceSegment_046_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 216 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 216 36 36, g32p_row19_traceSegment_046_0216_0036, g32p_row19_traceSegment_046_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 144 144 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 144 72 72, g32p_row19_traceSegment_046_0144_0072, g32p_row19_traceSegment_046_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_046 0 288 = [0, 4, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 144 144, g32p_row19_traceSegment_046_0000_0144, g32p_row19_traceSegment_046_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 297 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 288 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 288 9 9, g32p_row19_traceSegment_046_0288_0009, g32p_row19_traceSegment_046_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 306 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 306 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 306 9 9, g32p_row19_traceSegment_046_0306_0009, g32p_row19_traceSegment_046_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 288 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 288 18 18, g32p_row19_traceSegment_046_0288_0018, g32p_row19_traceSegment_046_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 333 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 324 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 324 9 9, g32p_row19_traceSegment_046_0324_0009, g32p_row19_traceSegment_046_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 342 9 9, g32p_row19_traceSegment_046_0342_0009, g32p_row19_traceSegment_046_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 324 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 324 18 18, g32p_row19_traceSegment_046_0324_0018, g32p_row19_traceSegment_046_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 288 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 288 36 36, g32p_row19_traceSegment_046_0288_0036, g32p_row19_traceSegment_046_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 360 9 9, g32p_row19_traceSegment_046_0360_0009, g32p_row19_traceSegment_046_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 378 9 9, g32p_row19_traceSegment_046_0378_0009, g32p_row19_traceSegment_046_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 360 18 18, g32p_row19_traceSegment_046_0360_0018, g32p_row19_traceSegment_046_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 396 9 9, g32p_row19_traceSegment_046_0396_0009, g32p_row19_traceSegment_046_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 414 9 9, g32p_row19_traceSegment_046_0414_0009, g32p_row19_traceSegment_046_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 396 18 18, g32p_row19_traceSegment_046_0396_0018, g32p_row19_traceSegment_046_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 360 36 36, g32p_row19_traceSegment_046_0360_0036, g32p_row19_traceSegment_046_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 288 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 288 72 72, g32p_row19_traceSegment_046_0288_0072, g32p_row19_traceSegment_046_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 441 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 432 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 432 9 9, g32p_row19_traceSegment_046_0432_0009, g32p_row19_traceSegment_046_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 459 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 450 9 9, g32p_row19_traceSegment_046_0450_0009, g32p_row19_traceSegment_046_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 432 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 432 18 18, g32p_row19_traceSegment_046_0432_0018, g32p_row19_traceSegment_046_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 468 9 9, g32p_row19_traceSegment_046_0468_0009, g32p_row19_traceSegment_046_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 486 9 9, g32p_row19_traceSegment_046_0486_0009, g32p_row19_traceSegment_046_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 468 18 18, g32p_row19_traceSegment_046_0468_0018, g32p_row19_traceSegment_046_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 432 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 432 36 36, g32p_row19_traceSegment_046_0432_0036, g32p_row19_traceSegment_046_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 513 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 504 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 504 9 9, g32p_row19_traceSegment_046_0504_0009, g32p_row19_traceSegment_046_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 522 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 531 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 522 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 522 9 9, g32p_row19_traceSegment_046_0522_0009, g32p_row19_traceSegment_046_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 504 36 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 504 18 18, g32p_row19_traceSegment_046_0504_0018, g32p_row19_traceSegment_046_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 540 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 549 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 540 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 540 9 9, g32p_row19_traceSegment_046_0540_0009, g32p_row19_traceSegment_046_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 558 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 567 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 558 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 558 9 9, g32p_row19_traceSegment_046_0558_0009, g32p_row19_traceSegment_046_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 540 36 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 540 18 18, g32p_row19_traceSegment_046_0540_0018, g32p_row19_traceSegment_046_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 504 72 = [0, 8, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 504 36 36, g32p_row19_traceSegment_046_0504_0036, g32p_row19_traceSegment_046_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 432 144 = [0, 10, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 432 72 72, g32p_row19_traceSegment_046_0432_0072, g32p_row19_traceSegment_046_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_046 288 288 = [0, 10, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 288 144 144, g32p_row19_traceSegment_046_0288_0144, g32p_row19_traceSegment_046_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_046 0 576 = [0, 14, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 288 288, g32p_row19_traceSegment_046_0000_0288, g32p_row19_traceSegment_046_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 576 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 585 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 576 18 = [0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 576 9 9, g32p_row19_traceSegment_046_0576_0009, g32p_row19_traceSegment_046_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 594 9 = [0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 603 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 594 18 = [0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 594 9 9, g32p_row19_traceSegment_046_0594_0009, g32p_row19_traceSegment_046_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 576 36 = [0, 4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 576 18 18, g32p_row19_traceSegment_046_0576_0018, g32p_row19_traceSegment_046_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 612 9 9, g32p_row19_traceSegment_046_0612_0009, g32p_row19_traceSegment_046_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 630 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 639 9 = [0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 630 18 = [0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 630 9 9, g32p_row19_traceSegment_046_0630_0009, g32p_row19_traceSegment_046_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 612 36 = [0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 612 18 18, g32p_row19_traceSegment_046_0612_0018, g32p_row19_traceSegment_046_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 576 72 = [0, 6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 576 36 36, g32p_row19_traceSegment_046_0576_0036, g32p_row19_traceSegment_046_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 648 9 9, g32p_row19_traceSegment_046_0648_0009, g32p_row19_traceSegment_046_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 666 9 9, g32p_row19_traceSegment_046_0666_0009, g32p_row19_traceSegment_046_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 648 18 18, g32p_row19_traceSegment_046_0648_0018, g32p_row19_traceSegment_046_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 684 9 9, g32p_row19_traceSegment_046_0684_0009, g32p_row19_traceSegment_046_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 702 9 = [0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 702 18 = [0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 702 9 9, g32p_row19_traceSegment_046_0702_0009, g32p_row19_traceSegment_046_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 684 36 = [0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 684 18 18, g32p_row19_traceSegment_046_0684_0018, g32p_row19_traceSegment_046_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 648 72 = [0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 648 36 36, g32p_row19_traceSegment_046_0648_0036, g32p_row19_traceSegment_046_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 576 144 = [0, 7, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 576 72 72, g32p_row19_traceSegment_046_0576_0072, g32p_row19_traceSegment_046_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 720 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 720 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 720 9 9, g32p_row19_traceSegment_046_0720_0009, g32p_row19_traceSegment_046_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 738 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 738 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 738 9 9, g32p_row19_traceSegment_046_0738_0009, g32p_row19_traceSegment_046_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 720 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 720 18 18, g32p_row19_traceSegment_046_0720_0018, g32p_row19_traceSegment_046_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 756 9 9, g32p_row19_traceSegment_046_0756_0009, g32p_row19_traceSegment_046_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 783 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 774 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 774 9 9, g32p_row19_traceSegment_046_0774_0009, g32p_row19_traceSegment_046_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 756 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 756 18 18, g32p_row19_traceSegment_046_0756_0018, g32p_row19_traceSegment_046_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 720 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 720 36 36, g32p_row19_traceSegment_046_0720_0036, g32p_row19_traceSegment_046_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 792 9 9, g32p_row19_traceSegment_046_0792_0009, g32p_row19_traceSegment_046_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 810 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 810 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 810 9 9, g32p_row19_traceSegment_046_0810_0009, g32p_row19_traceSegment_046_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 792 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 792 18 18, g32p_row19_traceSegment_046_0792_0018, g32p_row19_traceSegment_046_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 828 9 = [0, 2, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 837 9 = [0, 2, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 828 18 = [0, 4, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 828 9 9, g32p_row19_traceSegment_046_0828_0009, g32p_row19_traceSegment_046_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 846 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 846 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 846 9 9, g32p_row19_traceSegment_046_0846_0009, g32p_row19_traceSegment_046_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 828 36 = [0, 5, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 828 18 18, g32p_row19_traceSegment_046_0828_0018, g32p_row19_traceSegment_046_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 792 72 = [0, 6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 792 36 36, g32p_row19_traceSegment_046_0792_0036, g32p_row19_traceSegment_046_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 720 144 = [0, 9, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 720 72 72, g32p_row19_traceSegment_046_0720_0072, g32p_row19_traceSegment_046_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_046 576 288 = [0, 16, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 576 144 144, g32p_row19_traceSegment_046_0576_0144, g32p_row19_traceSegment_046_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 873 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 864 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 864 9 9, g32p_row19_traceSegment_046_0864_0009, g32p_row19_traceSegment_046_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 882 9 9, g32p_row19_traceSegment_046_0882_0009, g32p_row19_traceSegment_046_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 864 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 864 18 18, g32p_row19_traceSegment_046_0864_0018, g32p_row19_traceSegment_046_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 900 9 9, g32p_row19_traceSegment_046_0900_0009, g32p_row19_traceSegment_046_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 918 9 9, g32p_row19_traceSegment_046_0918_0009, g32p_row19_traceSegment_046_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 900 18 18, g32p_row19_traceSegment_046_0900_0018, g32p_row19_traceSegment_046_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 864 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 864 36 36, g32p_row19_traceSegment_046_0864_0036, g32p_row19_traceSegment_046_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 936 9 9, g32p_row19_traceSegment_046_0936_0009, g32p_row19_traceSegment_046_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 954 9 9, g32p_row19_traceSegment_046_0954_0009, g32p_row19_traceSegment_046_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 936 18 18, g32p_row19_traceSegment_046_0936_0018, g32p_row19_traceSegment_046_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 972 9 9, g32p_row19_traceSegment_046_0972_0009, g32p_row19_traceSegment_046_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 990 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 990 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 990 9 9, g32p_row19_traceSegment_046_0990_0009, g32p_row19_traceSegment_046_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 972 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 972 18 18, g32p_row19_traceSegment_046_0972_0018, g32p_row19_traceSegment_046_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 936 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 936 36 36, g32p_row19_traceSegment_046_0936_0036, g32p_row19_traceSegment_046_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 864 144 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 864 72 72, g32p_row19_traceSegment_046_0864_0072, g32p_row19_traceSegment_046_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1008 9 9, g32p_row19_traceSegment_046_1008_0009, g32p_row19_traceSegment_046_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1026 9 9, g32p_row19_traceSegment_046_1026_0009, g32p_row19_traceSegment_046_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1008 18 18, g32p_row19_traceSegment_046_1008_0018, g32p_row19_traceSegment_046_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1053 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1044 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1044 9 9, g32p_row19_traceSegment_046_1044_0009, g32p_row19_traceSegment_046_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1062 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1062 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1062 9 9, g32p_row19_traceSegment_046_1062_0009, g32p_row19_traceSegment_046_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 1044 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1044 18 18, g32p_row19_traceSegment_046_1044_0018, g32p_row19_traceSegment_046_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 1008 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1008 36 36, g32p_row19_traceSegment_046_1008_0036, g32p_row19_traceSegment_046_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1080 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1080 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1080 9 9, g32p_row19_traceSegment_046_1080_0009, g32p_row19_traceSegment_046_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1098 9 9, g32p_row19_traceSegment_046_1098_0009, g32p_row19_traceSegment_046_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 1080 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1080 18 18, g32p_row19_traceSegment_046_1080_0018, g32p_row19_traceSegment_046_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1116 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1116 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1116 9 9, g32p_row19_traceSegment_046_1116_0009, g32p_row19_traceSegment_046_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_046 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_046_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_046 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1134 9 9, g32p_row19_traceSegment_046_1134_0009, g32p_row19_traceSegment_046_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_046 1116 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1116 18 18, g32p_row19_traceSegment_046_1116_0018, g32p_row19_traceSegment_046_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_046 1080 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1080 36 36, g32p_row19_traceSegment_046_1080_0036, g32p_row19_traceSegment_046_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_046_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_046 1008 144 = [0, 2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 1008 72 72, g32p_row19_traceSegment_046_1008_0072, g32p_row19_traceSegment_046_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_046 864 288 = [0, 2, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 864 144 144, g32p_row19_traceSegment_046_0864_0144, g32p_row19_traceSegment_046_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_046 576 576 = [0, 18, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 576 288 288, g32p_row19_traceSegment_046_0576_0288, g32p_row19_traceSegment_046_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_046_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_046 0 1152 = [0, 32, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_046 0 576 576, g32p_row19_traceSegment_046_0000_0576, g32p_row19_traceSegment_046_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 46 = [0, 32, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_046_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_049_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 9 9, g32p_row19_traceSegment_049_0000_0009, g32p_row19_traceSegment_049_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 18 9 9, g32p_row19_traceSegment_049_0018_0009, g32p_row19_traceSegment_049_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 18 18, g32p_row19_traceSegment_049_0000_0018, g32p_row19_traceSegment_049_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 36 9 9, g32p_row19_traceSegment_049_0036_0009, g32p_row19_traceSegment_049_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 54 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 63 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 54 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 54 9 9, g32p_row19_traceSegment_049_0054_0009, g32p_row19_traceSegment_049_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 36 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 36 18 18, g32p_row19_traceSegment_049_0036_0018, g32p_row19_traceSegment_049_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 0 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 36 36, g32p_row19_traceSegment_049_0000_0036, g32p_row19_traceSegment_049_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 72 9 9, g32p_row19_traceSegment_049_0072_0009, g32p_row19_traceSegment_049_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 90 9 9, g32p_row19_traceSegment_049_0090_0009, g32p_row19_traceSegment_049_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 72 18 18, g32p_row19_traceSegment_049_0072_0018, g32p_row19_traceSegment_049_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 117 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 108 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 108 9 9, g32p_row19_traceSegment_049_0108_0009, g32p_row19_traceSegment_049_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 126 9 9, g32p_row19_traceSegment_049_0126_0009, g32p_row19_traceSegment_049_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 108 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 108 18 18, g32p_row19_traceSegment_049_0108_0018, g32p_row19_traceSegment_049_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 72 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 72 36 36, g32p_row19_traceSegment_049_0072_0036, g32p_row19_traceSegment_049_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 0 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 72 72, g32p_row19_traceSegment_049_0000_0072, g32p_row19_traceSegment_049_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 144 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 144 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 144 9 9, g32p_row19_traceSegment_049_0144_0009, g32p_row19_traceSegment_049_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 162 9 9, g32p_row19_traceSegment_049_0162_0009, g32p_row19_traceSegment_049_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 144 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 144 18 18, g32p_row19_traceSegment_049_0144_0018, g32p_row19_traceSegment_049_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 180 9 9, g32p_row19_traceSegment_049_0180_0009, g32p_row19_traceSegment_049_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 198 9 9, g32p_row19_traceSegment_049_0198_0009, g32p_row19_traceSegment_049_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 180 18 18, g32p_row19_traceSegment_049_0180_0018, g32p_row19_traceSegment_049_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 144 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 144 36 36, g32p_row19_traceSegment_049_0144_0036, g32p_row19_traceSegment_049_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 216 9 9, g32p_row19_traceSegment_049_0216_0009, g32p_row19_traceSegment_049_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 243 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 234 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 234 9 9, g32p_row19_traceSegment_049_0234_0009, g32p_row19_traceSegment_049_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 216 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 216 18 18, g32p_row19_traceSegment_049_0216_0018, g32p_row19_traceSegment_049_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 252 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 261 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 252 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 252 9 9, g32p_row19_traceSegment_049_0252_0009, g32p_row19_traceSegment_049_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 270 9 9, g32p_row19_traceSegment_049_0270_0009, g32p_row19_traceSegment_049_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 252 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 252 18 18, g32p_row19_traceSegment_049_0252_0018, g32p_row19_traceSegment_049_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 216 72 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 216 36 36, g32p_row19_traceSegment_049_0216_0036, g32p_row19_traceSegment_049_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 144 144 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 144 72 72, g32p_row19_traceSegment_049_0144_0072, g32p_row19_traceSegment_049_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_049 0 288 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 144 144, g32p_row19_traceSegment_049_0000_0144, g32p_row19_traceSegment_049_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 288 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 297 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 288 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 288 9 9, g32p_row19_traceSegment_049_0288_0009, g32p_row19_traceSegment_049_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 315 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 306 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 306 9 9, g32p_row19_traceSegment_049_0306_0009, g32p_row19_traceSegment_049_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 288 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 288 18 18, g32p_row19_traceSegment_049_0288_0018, g32p_row19_traceSegment_049_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 333 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 324 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 324 9 9, g32p_row19_traceSegment_049_0324_0009, g32p_row19_traceSegment_049_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 342 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 342 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 342 9 9, g32p_row19_traceSegment_049_0342_0009, g32p_row19_traceSegment_049_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 324 36 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 324 18 18, g32p_row19_traceSegment_049_0324_0018, g32p_row19_traceSegment_049_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 288 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 288 36 36, g32p_row19_traceSegment_049_0288_0036, g32p_row19_traceSegment_049_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 360 9 9, g32p_row19_traceSegment_049_0360_0009, g32p_row19_traceSegment_049_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 378 9 9, g32p_row19_traceSegment_049_0378_0009, g32p_row19_traceSegment_049_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 360 18 18, g32p_row19_traceSegment_049_0360_0018, g32p_row19_traceSegment_049_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 396 9 9, g32p_row19_traceSegment_049_0396_0009, g32p_row19_traceSegment_049_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 414 9 9, g32p_row19_traceSegment_049_0414_0009, g32p_row19_traceSegment_049_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 396 18 18, g32p_row19_traceSegment_049_0396_0018, g32p_row19_traceSegment_049_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 360 36 36, g32p_row19_traceSegment_049_0360_0036, g32p_row19_traceSegment_049_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 288 144 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 288 72 72, g32p_row19_traceSegment_049_0288_0072, g32p_row19_traceSegment_049_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 441 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 432 9 9, g32p_row19_traceSegment_049_0432_0009, g32p_row19_traceSegment_049_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 450 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 459 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 450 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 450 9 9, g32p_row19_traceSegment_049_0450_0009, g32p_row19_traceSegment_049_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 432 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 432 18 18, g32p_row19_traceSegment_049_0432_0018, g32p_row19_traceSegment_049_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 468 9 9, g32p_row19_traceSegment_049_0468_0009, g32p_row19_traceSegment_049_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 486 9 9, g32p_row19_traceSegment_049_0486_0009, g32p_row19_traceSegment_049_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 468 18 18, g32p_row19_traceSegment_049_0468_0018, g32p_row19_traceSegment_049_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 432 72 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 432 36 36, g32p_row19_traceSegment_049_0432_0036, g32p_row19_traceSegment_049_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 504 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 513 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 504 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 504 9 9, g32p_row19_traceSegment_049_0504_0009, g32p_row19_traceSegment_049_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 531 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 522 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 522 9 9, g32p_row19_traceSegment_049_0522_0009, g32p_row19_traceSegment_049_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 504 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 504 18 18, g32p_row19_traceSegment_049_0504_0018, g32p_row19_traceSegment_049_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 540 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 540 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 540 9 9, g32p_row19_traceSegment_049_0540_0009, g32p_row19_traceSegment_049_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 558 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 567 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 558 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 558 9 9, g32p_row19_traceSegment_049_0558_0009, g32p_row19_traceSegment_049_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 540 36 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 540 18 18, g32p_row19_traceSegment_049_0540_0018, g32p_row19_traceSegment_049_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 504 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 504 36 36, g32p_row19_traceSegment_049_0504_0036, g32p_row19_traceSegment_049_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 432 144 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 432 72 72, g32p_row19_traceSegment_049_0432_0072, g32p_row19_traceSegment_049_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_049 288 288 = [0, 0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 288 144 144, g32p_row19_traceSegment_049_0288_0144, g32p_row19_traceSegment_049_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_049 0 576 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 288 288, g32p_row19_traceSegment_049_0000_0288, g32p_row19_traceSegment_049_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 585 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 576 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 576 9 9, g32p_row19_traceSegment_049_0576_0009, g32p_row19_traceSegment_049_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 594 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 594 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 594 9 9, g32p_row19_traceSegment_049_0594_0009, g32p_row19_traceSegment_049_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 576 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 576 18 18, g32p_row19_traceSegment_049_0576_0018, g32p_row19_traceSegment_049_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 612 9 9, g32p_row19_traceSegment_049_0612_0009, g32p_row19_traceSegment_049_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 630 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 630 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 630 9 9, g32p_row19_traceSegment_049_0630_0009, g32p_row19_traceSegment_049_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 612 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 612 18 18, g32p_row19_traceSegment_049_0612_0018, g32p_row19_traceSegment_049_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 576 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 576 36 36, g32p_row19_traceSegment_049_0576_0036, g32p_row19_traceSegment_049_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 648 9 9, g32p_row19_traceSegment_049_0648_0009, g32p_row19_traceSegment_049_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 666 9 9, g32p_row19_traceSegment_049_0666_0009, g32p_row19_traceSegment_049_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 648 18 18, g32p_row19_traceSegment_049_0648_0018, g32p_row19_traceSegment_049_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 684 9 9, g32p_row19_traceSegment_049_0684_0009, g32p_row19_traceSegment_049_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 702 9 9, g32p_row19_traceSegment_049_0702_0009, g32p_row19_traceSegment_049_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 684 18 18, g32p_row19_traceSegment_049_0684_0018, g32p_row19_traceSegment_049_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 648 36 36, g32p_row19_traceSegment_049_0648_0036, g32p_row19_traceSegment_049_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 576 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 576 72 72, g32p_row19_traceSegment_049_0576_0072, g32p_row19_traceSegment_049_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 729 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 720 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 720 9 9, g32p_row19_traceSegment_049_0720_0009, g32p_row19_traceSegment_049_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 738 9 9, g32p_row19_traceSegment_049_0738_0009, g32p_row19_traceSegment_049_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 720 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 720 18 18, g32p_row19_traceSegment_049_0720_0018, g32p_row19_traceSegment_049_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 756 9 9, g32p_row19_traceSegment_049_0756_0009, g32p_row19_traceSegment_049_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 774 9 9, g32p_row19_traceSegment_049_0774_0009, g32p_row19_traceSegment_049_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 756 18 18, g32p_row19_traceSegment_049_0756_0018, g32p_row19_traceSegment_049_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 720 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 720 36 36, g32p_row19_traceSegment_049_0720_0036, g32p_row19_traceSegment_049_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 792 9 9, g32p_row19_traceSegment_049_0792_0009, g32p_row19_traceSegment_049_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 810 9 9, g32p_row19_traceSegment_049_0810_0009, g32p_row19_traceSegment_049_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 792 18 18, g32p_row19_traceSegment_049_0792_0018, g32p_row19_traceSegment_049_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 828 9 9, g32p_row19_traceSegment_049_0828_0009, g32p_row19_traceSegment_049_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 855 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 846 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 846 9 9, g32p_row19_traceSegment_049_0846_0009, g32p_row19_traceSegment_049_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 828 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 828 18 18, g32p_row19_traceSegment_049_0828_0018, g32p_row19_traceSegment_049_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 792 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 792 36 36, g32p_row19_traceSegment_049_0792_0036, g32p_row19_traceSegment_049_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 720 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 720 72 72, g32p_row19_traceSegment_049_0720_0072, g32p_row19_traceSegment_049_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_049 576 288 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 576 144 144, g32p_row19_traceSegment_049_0576_0144, g32p_row19_traceSegment_049_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 864 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 864 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 864 9 9, g32p_row19_traceSegment_049_0864_0009, g32p_row19_traceSegment_049_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 882 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 882 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 882 9 9, g32p_row19_traceSegment_049_0882_0009, g32p_row19_traceSegment_049_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 864 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 864 18 18, g32p_row19_traceSegment_049_0864_0018, g32p_row19_traceSegment_049_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 900 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 909 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 900 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 900 9 9, g32p_row19_traceSegment_049_0900_0009, g32p_row19_traceSegment_049_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 918 9 9, g32p_row19_traceSegment_049_0918_0009, g32p_row19_traceSegment_049_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 900 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 900 18 18, g32p_row19_traceSegment_049_0900_0018, g32p_row19_traceSegment_049_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 864 72 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 864 36 36, g32p_row19_traceSegment_049_0864_0036, g32p_row19_traceSegment_049_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 936 9 9, g32p_row19_traceSegment_049_0936_0009, g32p_row19_traceSegment_049_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 963 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 954 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 954 9 9, g32p_row19_traceSegment_049_0954_0009, g32p_row19_traceSegment_049_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 936 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 936 18 18, g32p_row19_traceSegment_049_0936_0018, g32p_row19_traceSegment_049_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 972 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 972 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 972 9 9, g32p_row19_traceSegment_049_0972_0009, g32p_row19_traceSegment_049_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 990 9 9, g32p_row19_traceSegment_049_0990_0009, g32p_row19_traceSegment_049_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 972 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 972 18 18, g32p_row19_traceSegment_049_0972_0018, g32p_row19_traceSegment_049_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 936 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 936 36 36, g32p_row19_traceSegment_049_0936_0036, g32p_row19_traceSegment_049_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 864 144 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 864 72 72, g32p_row19_traceSegment_049_0864_0072, g32p_row19_traceSegment_049_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1008 9 9, g32p_row19_traceSegment_049_1008_0009, g32p_row19_traceSegment_049_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1026 9 9, g32p_row19_traceSegment_049_1026_0009, g32p_row19_traceSegment_049_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1008 18 18, g32p_row19_traceSegment_049_1008_0018, g32p_row19_traceSegment_049_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1044 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1044 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1044 9 9, g32p_row19_traceSegment_049_1044_0009, g32p_row19_traceSegment_049_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1062 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1062 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1062 9 9, g32p_row19_traceSegment_049_1062_0009, g32p_row19_traceSegment_049_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 1044 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1044 18 18, g32p_row19_traceSegment_049_1044_0018, g32p_row19_traceSegment_049_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 1008 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1008 36 36, g32p_row19_traceSegment_049_1008_0036, g32p_row19_traceSegment_049_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1089 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1080 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1080 9 9, g32p_row19_traceSegment_049_1080_0009, g32p_row19_traceSegment_049_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1098 9 9, g32p_row19_traceSegment_049_1098_0009, g32p_row19_traceSegment_049_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 1080 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1080 18 18, g32p_row19_traceSegment_049_1080_0018, g32p_row19_traceSegment_049_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1116 9 9, g32p_row19_traceSegment_049_1116_0009, g32p_row19_traceSegment_049_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1134 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_049 1143 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_049_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_049 1134 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1134 9 9, g32p_row19_traceSegment_049_1134_0009, g32p_row19_traceSegment_049_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_049 1116 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1116 18 18, g32p_row19_traceSegment_049_1116_0018, g32p_row19_traceSegment_049_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_049 1080 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1080 36 36, g32p_row19_traceSegment_049_1080_0036, g32p_row19_traceSegment_049_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_049_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_049 1008 144 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 1008 72 72, g32p_row19_traceSegment_049_1008_0072, g32p_row19_traceSegment_049_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_049 864 288 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 864 144 144, g32p_row19_traceSegment_049_0864_0144, g32p_row19_traceSegment_049_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_049 576 576 = [0, 0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 576 288 288, g32p_row19_traceSegment_049_0576_0288, g32p_row19_traceSegment_049_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_049_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_049 0 1152 = [0, 0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_049 0 576 576, g32p_row19_traceSegment_049_0000_0576, g32p_row19_traceSegment_049_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 49 = [0, 0, 0, 0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_049_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_050 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 50 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_050_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 9 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 0 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 9 9, g32p_row19_traceSegment_050_0000_0009, g32p_row19_traceSegment_050_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 18 9 9, g32p_row19_traceSegment_050_0018_0009, g32p_row19_traceSegment_050_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 0 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 18 18, g32p_row19_traceSegment_050_0000_0018, g32p_row19_traceSegment_050_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 36 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 36 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 36 9 9, g32p_row19_traceSegment_050_0036_0009, g32p_row19_traceSegment_050_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 54 9 9, g32p_row19_traceSegment_050_0054_0009, g32p_row19_traceSegment_050_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 36 18 18, g32p_row19_traceSegment_050_0036_0018, g32p_row19_traceSegment_050_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 0 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 36 36, g32p_row19_traceSegment_050_0000_0036, g32p_row19_traceSegment_050_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 72 9 9, g32p_row19_traceSegment_050_0072_0009, g32p_row19_traceSegment_050_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 90 9 9, g32p_row19_traceSegment_050_0090_0009, g32p_row19_traceSegment_050_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 72 18 18, g32p_row19_traceSegment_050_0072_0018, g32p_row19_traceSegment_050_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 117 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 108 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 108 9 9, g32p_row19_traceSegment_050_0108_0009, g32p_row19_traceSegment_050_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 135 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 126 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 126 9 9, g32p_row19_traceSegment_050_0126_0009, g32p_row19_traceSegment_050_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 108 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 108 18 18, g32p_row19_traceSegment_050_0108_0018, g32p_row19_traceSegment_050_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 72 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 72 36 36, g32p_row19_traceSegment_050_0072_0036, g32p_row19_traceSegment_050_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 0 144 = [0, 0, 0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 72 72, g32p_row19_traceSegment_050_0000_0072, g32p_row19_traceSegment_050_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 153 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 144 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 144 9 9, g32p_row19_traceSegment_050_0144_0009, g32p_row19_traceSegment_050_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 171 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 162 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 162 9 9, g32p_row19_traceSegment_050_0162_0009, g32p_row19_traceSegment_050_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 144 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 144 18 18, g32p_row19_traceSegment_050_0144_0018, g32p_row19_traceSegment_050_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 180 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 180 18 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 180 9 9, g32p_row19_traceSegment_050_0180_0009, g32p_row19_traceSegment_050_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 198 9 9, g32p_row19_traceSegment_050_0198_0009, g32p_row19_traceSegment_050_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 180 36 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 180 18 18, g32p_row19_traceSegment_050_0180_0018, g32p_row19_traceSegment_050_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 144 72 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 144 36 36, g32p_row19_traceSegment_050_0144_0036, g32p_row19_traceSegment_050_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 216 9 9, g32p_row19_traceSegment_050_0216_0009, g32p_row19_traceSegment_050_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 234 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 234 9 9, g32p_row19_traceSegment_050_0234_0009, g32p_row19_traceSegment_050_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 216 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 216 18 18, g32p_row19_traceSegment_050_0216_0018, g32p_row19_traceSegment_050_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 261 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 252 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 252 9 9, g32p_row19_traceSegment_050_0252_0009, g32p_row19_traceSegment_050_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 270 9 9, g32p_row19_traceSegment_050_0270_0009, g32p_row19_traceSegment_050_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 252 18 18, g32p_row19_traceSegment_050_0252_0018, g32p_row19_traceSegment_050_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 216 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 216 36 36, g32p_row19_traceSegment_050_0216_0036, g32p_row19_traceSegment_050_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 144 144 = [0, 0, 0, 5, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 144 72 72, g32p_row19_traceSegment_050_0144_0072, g32p_row19_traceSegment_050_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_050 0 288 = [0, 0, 0, 7, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 144 144, g32p_row19_traceSegment_050_0000_0144, g32p_row19_traceSegment_050_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 297 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 288 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 288 9 9, g32p_row19_traceSegment_050_0288_0009, g32p_row19_traceSegment_050_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 306 9 9, g32p_row19_traceSegment_050_0306_0009, g32p_row19_traceSegment_050_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 288 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 288 18 18, g32p_row19_traceSegment_050_0288_0018, g32p_row19_traceSegment_050_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 333 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 324 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 324 9 9, g32p_row19_traceSegment_050_0324_0009, g32p_row19_traceSegment_050_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 342 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 351 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 342 18 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 342 9 9, g32p_row19_traceSegment_050_0342_0009, g32p_row19_traceSegment_050_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 324 36 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 324 18 18, g32p_row19_traceSegment_050_0324_0018, g32p_row19_traceSegment_050_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 288 72 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 288 36 36, g32p_row19_traceSegment_050_0288_0036, g32p_row19_traceSegment_050_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 369 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 360 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 360 9 9, g32p_row19_traceSegment_050_0360_0009, g32p_row19_traceSegment_050_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 378 9 9, g32p_row19_traceSegment_050_0378_0009, g32p_row19_traceSegment_050_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 360 18 18, g32p_row19_traceSegment_050_0360_0018, g32p_row19_traceSegment_050_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 396 9 9, g32p_row19_traceSegment_050_0396_0009, g32p_row19_traceSegment_050_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 414 9 9, g32p_row19_traceSegment_050_0414_0009, g32p_row19_traceSegment_050_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 396 18 18, g32p_row19_traceSegment_050_0396_0018, g32p_row19_traceSegment_050_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 360 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 360 36 36, g32p_row19_traceSegment_050_0360_0036, g32p_row19_traceSegment_050_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 288 144 = [0, 0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 288 72 72, g32p_row19_traceSegment_050_0288_0072, g32p_row19_traceSegment_050_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 432 9 9, g32p_row19_traceSegment_050_0432_0009, g32p_row19_traceSegment_050_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 450 9 9, g32p_row19_traceSegment_050_0450_0009, g32p_row19_traceSegment_050_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 432 18 18, g32p_row19_traceSegment_050_0432_0018, g32p_row19_traceSegment_050_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 477 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 468 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 468 9 9, g32p_row19_traceSegment_050_0468_0009, g32p_row19_traceSegment_050_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 486 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 486 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 486 9 9, g32p_row19_traceSegment_050_0486_0009, g32p_row19_traceSegment_050_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 468 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 468 18 18, g32p_row19_traceSegment_050_0468_0018, g32p_row19_traceSegment_050_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 432 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 432 36 36, g32p_row19_traceSegment_050_0432_0036, g32p_row19_traceSegment_050_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 513 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 504 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 504 9 9, g32p_row19_traceSegment_050_0504_0009, g32p_row19_traceSegment_050_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 522 9 9, g32p_row19_traceSegment_050_0522_0009, g32p_row19_traceSegment_050_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 504 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 504 18 18, g32p_row19_traceSegment_050_0504_0018, g32p_row19_traceSegment_050_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 540 9 9, g32p_row19_traceSegment_050_0540_0009, g32p_row19_traceSegment_050_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 558 9 9, g32p_row19_traceSegment_050_0558_0009, g32p_row19_traceSegment_050_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 540 18 18, g32p_row19_traceSegment_050_0540_0018, g32p_row19_traceSegment_050_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 504 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 504 36 36, g32p_row19_traceSegment_050_0504_0036, g32p_row19_traceSegment_050_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 432 144 = [0, 0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 432 72 72, g32p_row19_traceSegment_050_0432_0072, g32p_row19_traceSegment_050_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_050 288 288 = [0, 0, 0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 288 144 144, g32p_row19_traceSegment_050_0288_0144, g32p_row19_traceSegment_050_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_050 0 576 = [0, 0, 0, 11, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 288 288, g32p_row19_traceSegment_050_0000_0288, g32p_row19_traceSegment_050_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 585 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 576 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 576 9 9, g32p_row19_traceSegment_050_0576_0009, g32p_row19_traceSegment_050_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 594 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 594 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 594 9 9, g32p_row19_traceSegment_050_0594_0009, g32p_row19_traceSegment_050_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 576 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 576 18 18, g32p_row19_traceSegment_050_0576_0018, g32p_row19_traceSegment_050_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 621 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 612 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 612 9 9, g32p_row19_traceSegment_050_0612_0009, g32p_row19_traceSegment_050_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 630 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 630 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 630 9 9, g32p_row19_traceSegment_050_0630_0009, g32p_row19_traceSegment_050_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 612 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 612 18 18, g32p_row19_traceSegment_050_0612_0018, g32p_row19_traceSegment_050_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 576 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 576 36 36, g32p_row19_traceSegment_050_0576_0036, g32p_row19_traceSegment_050_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 648 9 9, g32p_row19_traceSegment_050_0648_0009, g32p_row19_traceSegment_050_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 666 9 9, g32p_row19_traceSegment_050_0666_0009, g32p_row19_traceSegment_050_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 648 18 18, g32p_row19_traceSegment_050_0648_0018, g32p_row19_traceSegment_050_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 684 9 9, g32p_row19_traceSegment_050_0684_0009, g32p_row19_traceSegment_050_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 702 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 702 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 702 9 9, g32p_row19_traceSegment_050_0702_0009, g32p_row19_traceSegment_050_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 684 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 684 18 18, g32p_row19_traceSegment_050_0684_0018, g32p_row19_traceSegment_050_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 648 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 648 36 36, g32p_row19_traceSegment_050_0648_0036, g32p_row19_traceSegment_050_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 576 144 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 576 72 72, g32p_row19_traceSegment_050_0576_0072, g32p_row19_traceSegment_050_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 720 9 9, g32p_row19_traceSegment_050_0720_0009, g32p_row19_traceSegment_050_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 747 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 738 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 738 9 9, g32p_row19_traceSegment_050_0738_0009, g32p_row19_traceSegment_050_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 720 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 720 18 18, g32p_row19_traceSegment_050_0720_0018, g32p_row19_traceSegment_050_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 756 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 756 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 756 9 9, g32p_row19_traceSegment_050_0756_0009, g32p_row19_traceSegment_050_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 783 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 774 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 774 9 9, g32p_row19_traceSegment_050_0774_0009, g32p_row19_traceSegment_050_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 756 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 756 18 18, g32p_row19_traceSegment_050_0756_0018, g32p_row19_traceSegment_050_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 720 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 720 36 36, g32p_row19_traceSegment_050_0720_0036, g32p_row19_traceSegment_050_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 792 9 9, g32p_row19_traceSegment_050_0792_0009, g32p_row19_traceSegment_050_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 810 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 810 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 810 9 9, g32p_row19_traceSegment_050_0810_0009, g32p_row19_traceSegment_050_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 792 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 792 18 18, g32p_row19_traceSegment_050_0792_0018, g32p_row19_traceSegment_050_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 837 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 828 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 828 9 9, g32p_row19_traceSegment_050_0828_0009, g32p_row19_traceSegment_050_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 846 9 = [0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 855 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 846 18 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 846 9 9, g32p_row19_traceSegment_050_0846_0009, g32p_row19_traceSegment_050_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 828 36 = [0, 0, 0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 828 18 18, g32p_row19_traceSegment_050_0828_0018, g32p_row19_traceSegment_050_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 792 72 = [0, 0, 0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 792 36 36, g32p_row19_traceSegment_050_0792_0036, g32p_row19_traceSegment_050_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 720 144 = [0, 0, 0, 6, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 720 72 72, g32p_row19_traceSegment_050_0720_0072, g32p_row19_traceSegment_050_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_050 576 288 = [0, 0, 0, 12, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 576 144 144, g32p_row19_traceSegment_050_0576_0144, g32p_row19_traceSegment_050_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 864 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 873 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 864 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 864 9 9, g32p_row19_traceSegment_050_0864_0009, g32p_row19_traceSegment_050_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 882 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 882 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 882 9 9, g32p_row19_traceSegment_050_0882_0009, g32p_row19_traceSegment_050_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 864 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 864 18 18, g32p_row19_traceSegment_050_0864_0018, g32p_row19_traceSegment_050_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 900 9 = [0, 0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 900 18 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 900 9 9, g32p_row19_traceSegment_050_0900_0009, g32p_row19_traceSegment_050_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 918 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 927 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 918 18 = [0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 918 9 9, g32p_row19_traceSegment_050_0918_0009, g32p_row19_traceSegment_050_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 900 36 = [0, 0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 900 18 18, g32p_row19_traceSegment_050_0900_0018, g32p_row19_traceSegment_050_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 864 72 = [0, 0, 0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 864 36 36, g32p_row19_traceSegment_050_0864_0036, g32p_row19_traceSegment_050_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 936 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 936 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 936 9 9, g32p_row19_traceSegment_050_0936_0009, g32p_row19_traceSegment_050_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 954 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 963 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 954 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 954 9 9, g32p_row19_traceSegment_050_0954_0009, g32p_row19_traceSegment_050_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 936 36 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 936 18 18, g32p_row19_traceSegment_050_0936_0018, g32p_row19_traceSegment_050_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 972 9 9, g32p_row19_traceSegment_050_0972_0009, g32p_row19_traceSegment_050_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 990 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 999 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 990 18 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 990 9 9, g32p_row19_traceSegment_050_0990_0009, g32p_row19_traceSegment_050_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 972 36 = [0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 972 18 18, g32p_row19_traceSegment_050_0972_0018, g32p_row19_traceSegment_050_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 936 72 = [0, 0, 0, 2, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 936 36 36, g32p_row19_traceSegment_050_0936_0036, g32p_row19_traceSegment_050_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 864 144 = [0, 0, 0, 9, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 864 72 72, g32p_row19_traceSegment_050_0864_0072, g32p_row19_traceSegment_050_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1008 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1017 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1008 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1008 9 9, g32p_row19_traceSegment_050_1008_0009, g32p_row19_traceSegment_050_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1026 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1035 9 = [0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1026 18 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1026 9 9, g32p_row19_traceSegment_050_1026_0009, g32p_row19_traceSegment_050_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 1008 36 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1008 18 18, g32p_row19_traceSegment_050_1008_0018, g32p_row19_traceSegment_050_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1044 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1044 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1044 9 9, g32p_row19_traceSegment_050_1044_0009, g32p_row19_traceSegment_050_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1062 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1062 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1062 9 9, g32p_row19_traceSegment_050_1062_0009, g32p_row19_traceSegment_050_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 1044 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1044 18 18, g32p_row19_traceSegment_050_1044_0018, g32p_row19_traceSegment_050_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 1008 72 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1008 36 36, g32p_row19_traceSegment_050_1008_0036, g32p_row19_traceSegment_050_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1080 9 9, g32p_row19_traceSegment_050_1080_0009, g32p_row19_traceSegment_050_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1098 9 9, g32p_row19_traceSegment_050_1098_0009, g32p_row19_traceSegment_050_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1080 18 18, g32p_row19_traceSegment_050_1080_0018, g32p_row19_traceSegment_050_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1116 9 9, g32p_row19_traceSegment_050_1116_0009, g32p_row19_traceSegment_050_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_050 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_050_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_050 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1134 9 9, g32p_row19_traceSegment_050_1134_0009, g32p_row19_traceSegment_050_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_050 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1116 18 18, g32p_row19_traceSegment_050_1116_0018, g32p_row19_traceSegment_050_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_050 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1080 36 36, g32p_row19_traceSegment_050_1080_0036, g32p_row19_traceSegment_050_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_050_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_050 1008 144 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 1008 72 72, g32p_row19_traceSegment_050_1008_0072, g32p_row19_traceSegment_050_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_050 864 288 = [0, 0, 0, 9, 19] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 864 144 144, g32p_row19_traceSegment_050_0864_0144, g32p_row19_traceSegment_050_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_050 576 576 = [0, 0, 0, 21, 23] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 576 288 288, g32p_row19_traceSegment_050_0576_0288, g32p_row19_traceSegment_050_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_050_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_050 0 1152 = [0, 0, 0, 32, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_050 0 576 576, g32p_row19_traceSegment_050_0000_0576, g32p_row19_traceSegment_050_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 50 = [0, 0, 0, 32, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_050_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_052 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 52 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_052_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 0 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 9 9, g32p_row19_traceSegment_052_0000_0009, g32p_row19_traceSegment_052_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 18 9 9, g32p_row19_traceSegment_052_0018_0009, g32p_row19_traceSegment_052_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 18 18, g32p_row19_traceSegment_052_0000_0018, g32p_row19_traceSegment_052_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 36 9 9, g32p_row19_traceSegment_052_0036_0009, g32p_row19_traceSegment_052_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 54 9 9, g32p_row19_traceSegment_052_0054_0009, g32p_row19_traceSegment_052_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 36 18 18, g32p_row19_traceSegment_052_0036_0018, g32p_row19_traceSegment_052_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 36 36, g32p_row19_traceSegment_052_0000_0036, g32p_row19_traceSegment_052_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 72 9 9, g32p_row19_traceSegment_052_0072_0009, g32p_row19_traceSegment_052_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 90 9 9, g32p_row19_traceSegment_052_0090_0009, g32p_row19_traceSegment_052_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 72 18 18, g32p_row19_traceSegment_052_0072_0018, g32p_row19_traceSegment_052_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 108 9 9, g32p_row19_traceSegment_052_0108_0009, g32p_row19_traceSegment_052_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 126 9 9, g32p_row19_traceSegment_052_0126_0009, g32p_row19_traceSegment_052_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 108 18 18, g32p_row19_traceSegment_052_0108_0018, g32p_row19_traceSegment_052_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 72 36 36, g32p_row19_traceSegment_052_0072_0036, g32p_row19_traceSegment_052_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 0 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 72 72, g32p_row19_traceSegment_052_0000_0072, g32p_row19_traceSegment_052_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 144 9 9, g32p_row19_traceSegment_052_0144_0009, g32p_row19_traceSegment_052_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 162 9 9, g32p_row19_traceSegment_052_0162_0009, g32p_row19_traceSegment_052_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 144 18 18, g32p_row19_traceSegment_052_0144_0018, g32p_row19_traceSegment_052_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 180 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 189 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 180 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 180 9 9, g32p_row19_traceSegment_052_0180_0009, g32p_row19_traceSegment_052_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 198 9 9, g32p_row19_traceSegment_052_0198_0009, g32p_row19_traceSegment_052_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 180 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 180 18 18, g32p_row19_traceSegment_052_0180_0018, g32p_row19_traceSegment_052_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 144 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 144 36 36, g32p_row19_traceSegment_052_0144_0036, g32p_row19_traceSegment_052_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 216 9 9, g32p_row19_traceSegment_052_0216_0009, g32p_row19_traceSegment_052_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 234 9 9, g32p_row19_traceSegment_052_0234_0009, g32p_row19_traceSegment_052_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 216 18 18, g32p_row19_traceSegment_052_0216_0018, g32p_row19_traceSegment_052_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 252 9 9, g32p_row19_traceSegment_052_0252_0009, g32p_row19_traceSegment_052_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 270 9 9, g32p_row19_traceSegment_052_0270_0009, g32p_row19_traceSegment_052_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 252 18 18, g32p_row19_traceSegment_052_0252_0018, g32p_row19_traceSegment_052_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 216 36 36, g32p_row19_traceSegment_052_0216_0036, g32p_row19_traceSegment_052_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 144 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 144 72 72, g32p_row19_traceSegment_052_0144_0072, g32p_row19_traceSegment_052_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_052 0 288 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 144 144, g32p_row19_traceSegment_052_0000_0144, g32p_row19_traceSegment_052_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 288 9 9, g32p_row19_traceSegment_052_0288_0009, g32p_row19_traceSegment_052_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 306 9 9, g32p_row19_traceSegment_052_0306_0009, g32p_row19_traceSegment_052_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 288 18 18, g32p_row19_traceSegment_052_0288_0018, g32p_row19_traceSegment_052_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 324 9 9, g32p_row19_traceSegment_052_0324_0009, g32p_row19_traceSegment_052_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 342 9 9, g32p_row19_traceSegment_052_0342_0009, g32p_row19_traceSegment_052_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 324 18 18, g32p_row19_traceSegment_052_0324_0018, g32p_row19_traceSegment_052_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 288 36 36, g32p_row19_traceSegment_052_0288_0036, g32p_row19_traceSegment_052_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 360 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 360 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 360 9 9, g32p_row19_traceSegment_052_0360_0009, g32p_row19_traceSegment_052_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 387 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 378 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 378 9 9, g32p_row19_traceSegment_052_0378_0009, g32p_row19_traceSegment_052_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 360 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 360 18 18, g32p_row19_traceSegment_052_0360_0018, g32p_row19_traceSegment_052_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 396 9 9, g32p_row19_traceSegment_052_0396_0009, g32p_row19_traceSegment_052_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 414 9 9, g32p_row19_traceSegment_052_0414_0009, g32p_row19_traceSegment_052_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 396 18 18, g32p_row19_traceSegment_052_0396_0018, g32p_row19_traceSegment_052_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 360 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 360 36 36, g32p_row19_traceSegment_052_0360_0036, g32p_row19_traceSegment_052_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 288 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 288 72 72, g32p_row19_traceSegment_052_0288_0072, g32p_row19_traceSegment_052_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 432 9 9, g32p_row19_traceSegment_052_0432_0009, g32p_row19_traceSegment_052_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 450 9 9, g32p_row19_traceSegment_052_0450_0009, g32p_row19_traceSegment_052_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 432 18 18, g32p_row19_traceSegment_052_0432_0018, g32p_row19_traceSegment_052_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 468 9 9, g32p_row19_traceSegment_052_0468_0009, g32p_row19_traceSegment_052_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 486 9 9, g32p_row19_traceSegment_052_0486_0009, g32p_row19_traceSegment_052_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 468 18 18, g32p_row19_traceSegment_052_0468_0018, g32p_row19_traceSegment_052_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 432 36 36, g32p_row19_traceSegment_052_0432_0036, g32p_row19_traceSegment_052_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 504 9 9, g32p_row19_traceSegment_052_0504_0009, g32p_row19_traceSegment_052_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 522 9 9, g32p_row19_traceSegment_052_0522_0009, g32p_row19_traceSegment_052_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 504 18 18, g32p_row19_traceSegment_052_0504_0018, g32p_row19_traceSegment_052_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 540 9 9, g32p_row19_traceSegment_052_0540_0009, g32p_row19_traceSegment_052_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 558 9 9, g32p_row19_traceSegment_052_0558_0009, g32p_row19_traceSegment_052_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 540 18 18, g32p_row19_traceSegment_052_0540_0018, g32p_row19_traceSegment_052_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 504 36 36, g32p_row19_traceSegment_052_0504_0036, g32p_row19_traceSegment_052_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 432 72 72, g32p_row19_traceSegment_052_0432_0072, g32p_row19_traceSegment_052_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_052 288 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 288 144 144, g32p_row19_traceSegment_052_0288_0144, g32p_row19_traceSegment_052_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_052 0 576 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 288 288, g32p_row19_traceSegment_052_0000_0288, g32p_row19_traceSegment_052_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 576 9 9, g32p_row19_traceSegment_052_0576_0009, g32p_row19_traceSegment_052_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 594 9 9, g32p_row19_traceSegment_052_0594_0009, g32p_row19_traceSegment_052_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 576 18 18, g32p_row19_traceSegment_052_0576_0018, g32p_row19_traceSegment_052_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 612 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 612 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 612 9 9, g32p_row19_traceSegment_052_0612_0009, g32p_row19_traceSegment_052_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 630 9 9, g32p_row19_traceSegment_052_0630_0009, g32p_row19_traceSegment_052_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 612 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 612 18 18, g32p_row19_traceSegment_052_0612_0018, g32p_row19_traceSegment_052_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 576 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 576 36 36, g32p_row19_traceSegment_052_0576_0036, g32p_row19_traceSegment_052_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 648 9 9, g32p_row19_traceSegment_052_0648_0009, g32p_row19_traceSegment_052_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 666 9 9, g32p_row19_traceSegment_052_0666_0009, g32p_row19_traceSegment_052_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 648 18 18, g32p_row19_traceSegment_052_0648_0018, g32p_row19_traceSegment_052_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 684 9 9, g32p_row19_traceSegment_052_0684_0009, g32p_row19_traceSegment_052_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 702 9 9, g32p_row19_traceSegment_052_0702_0009, g32p_row19_traceSegment_052_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 684 18 18, g32p_row19_traceSegment_052_0684_0018, g32p_row19_traceSegment_052_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 648 36 36, g32p_row19_traceSegment_052_0648_0036, g32p_row19_traceSegment_052_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 576 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 576 72 72, g32p_row19_traceSegment_052_0576_0072, g32p_row19_traceSegment_052_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 720 9 9, g32p_row19_traceSegment_052_0720_0009, g32p_row19_traceSegment_052_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 747 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 738 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 738 9 9, g32p_row19_traceSegment_052_0738_0009, g32p_row19_traceSegment_052_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 720 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 720 18 18, g32p_row19_traceSegment_052_0720_0018, g32p_row19_traceSegment_052_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 756 9 9, g32p_row19_traceSegment_052_0756_0009, g32p_row19_traceSegment_052_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 774 9 9, g32p_row19_traceSegment_052_0774_0009, g32p_row19_traceSegment_052_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 756 18 18, g32p_row19_traceSegment_052_0756_0018, g32p_row19_traceSegment_052_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 720 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 720 36 36, g32p_row19_traceSegment_052_0720_0036, g32p_row19_traceSegment_052_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 792 9 9, g32p_row19_traceSegment_052_0792_0009, g32p_row19_traceSegment_052_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 810 9 9, g32p_row19_traceSegment_052_0810_0009, g32p_row19_traceSegment_052_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 792 18 18, g32p_row19_traceSegment_052_0792_0018, g32p_row19_traceSegment_052_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 828 9 9, g32p_row19_traceSegment_052_0828_0009, g32p_row19_traceSegment_052_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 846 9 9, g32p_row19_traceSegment_052_0846_0009, g32p_row19_traceSegment_052_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 828 18 18, g32p_row19_traceSegment_052_0828_0018, g32p_row19_traceSegment_052_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 792 36 36, g32p_row19_traceSegment_052_0792_0036, g32p_row19_traceSegment_052_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 720 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 720 72 72, g32p_row19_traceSegment_052_0720_0072, g32p_row19_traceSegment_052_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_052 576 288 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 576 144 144, g32p_row19_traceSegment_052_0576_0144, g32p_row19_traceSegment_052_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 864 9 9, g32p_row19_traceSegment_052_0864_0009, g32p_row19_traceSegment_052_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 882 9 9, g32p_row19_traceSegment_052_0882_0009, g32p_row19_traceSegment_052_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 864 18 18, g32p_row19_traceSegment_052_0864_0018, g32p_row19_traceSegment_052_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 900 9 9, g32p_row19_traceSegment_052_0900_0009, g32p_row19_traceSegment_052_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 918 9 9, g32p_row19_traceSegment_052_0918_0009, g32p_row19_traceSegment_052_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 900 18 18, g32p_row19_traceSegment_052_0900_0018, g32p_row19_traceSegment_052_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 864 36 36, g32p_row19_traceSegment_052_0864_0036, g32p_row19_traceSegment_052_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 936 9 9, g32p_row19_traceSegment_052_0936_0009, g32p_row19_traceSegment_052_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 954 9 9, g32p_row19_traceSegment_052_0954_0009, g32p_row19_traceSegment_052_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 936 18 18, g32p_row19_traceSegment_052_0936_0018, g32p_row19_traceSegment_052_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 972 9 9, g32p_row19_traceSegment_052_0972_0009, g32p_row19_traceSegment_052_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 990 9 9, g32p_row19_traceSegment_052_0990_0009, g32p_row19_traceSegment_052_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 972 18 18, g32p_row19_traceSegment_052_0972_0018, g32p_row19_traceSegment_052_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 936 36 36, g32p_row19_traceSegment_052_0936_0036, g32p_row19_traceSegment_052_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 864 72 72, g32p_row19_traceSegment_052_0864_0072, g32p_row19_traceSegment_052_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1008 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1017 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1008 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1008 9 9, g32p_row19_traceSegment_052_1008_0009, g32p_row19_traceSegment_052_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1026 9 9, g32p_row19_traceSegment_052_1026_0009, g32p_row19_traceSegment_052_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 1008 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1008 18 18, g32p_row19_traceSegment_052_1008_0018, g32p_row19_traceSegment_052_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1044 9 9, g32p_row19_traceSegment_052_1044_0009, g32p_row19_traceSegment_052_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1062 9 9, g32p_row19_traceSegment_052_1062_0009, g32p_row19_traceSegment_052_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1044 18 18, g32p_row19_traceSegment_052_1044_0018, g32p_row19_traceSegment_052_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 1008 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1008 36 36, g32p_row19_traceSegment_052_1008_0036, g32p_row19_traceSegment_052_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1080 9 9, g32p_row19_traceSegment_052_1080_0009, g32p_row19_traceSegment_052_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1098 9 9, g32p_row19_traceSegment_052_1098_0009, g32p_row19_traceSegment_052_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1080 18 18, g32p_row19_traceSegment_052_1080_0018, g32p_row19_traceSegment_052_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1116 9 9, g32p_row19_traceSegment_052_1116_0009, g32p_row19_traceSegment_052_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_052 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_052_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_052 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1134 9 9, g32p_row19_traceSegment_052_1134_0009, g32p_row19_traceSegment_052_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_052 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1116 18 18, g32p_row19_traceSegment_052_1116_0018, g32p_row19_traceSegment_052_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_052 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1080 36 36, g32p_row19_traceSegment_052_1080_0036, g32p_row19_traceSegment_052_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_052_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_052 1008 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 1008 72 72, g32p_row19_traceSegment_052_1008_0072, g32p_row19_traceSegment_052_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_052 864 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 864 144 144, g32p_row19_traceSegment_052_0864_0144, g32p_row19_traceSegment_052_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_052 576 576 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 576 288 288, g32p_row19_traceSegment_052_0576_0288, g32p_row19_traceSegment_052_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_052_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_052 0 1152 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_052 0 576 576, g32p_row19_traceSegment_052_0000_0576, g32p_row19_traceSegment_052_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 52 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_052_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_056_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 9 9, g32p_row19_traceSegment_056_0000_0009, g32p_row19_traceSegment_056_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 18 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 18 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 18 9 9, g32p_row19_traceSegment_056_0018_0009, g32p_row19_traceSegment_056_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 18 18, g32p_row19_traceSegment_056_0000_0018, g32p_row19_traceSegment_056_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 36 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 36 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 36 9 9, g32p_row19_traceSegment_056_0036_0009, g32p_row19_traceSegment_056_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 54 9 9, g32p_row19_traceSegment_056_0054_0009, g32p_row19_traceSegment_056_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 36 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 36 18 18, g32p_row19_traceSegment_056_0036_0018, g32p_row19_traceSegment_056_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 0 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 36 36, g32p_row19_traceSegment_056_0000_0036, g32p_row19_traceSegment_056_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 72 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 72 9 9, g32p_row19_traceSegment_056_0072_0009, g32p_row19_traceSegment_056_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 90 9 9, g32p_row19_traceSegment_056_0090_0009, g32p_row19_traceSegment_056_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 72 18 18, g32p_row19_traceSegment_056_0072_0018, g32p_row19_traceSegment_056_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 108 9 9, g32p_row19_traceSegment_056_0108_0009, g32p_row19_traceSegment_056_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 126 9 9, g32p_row19_traceSegment_056_0126_0009, g32p_row19_traceSegment_056_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 108 18 18, g32p_row19_traceSegment_056_0108_0018, g32p_row19_traceSegment_056_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 72 36 36, g32p_row19_traceSegment_056_0072_0036, g32p_row19_traceSegment_056_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 0 144 = [3, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 72 72, g32p_row19_traceSegment_056_0000_0072, g32p_row19_traceSegment_056_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 144 9 9, g32p_row19_traceSegment_056_0144_0009, g32p_row19_traceSegment_056_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 162 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 162 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 162 9 9, g32p_row19_traceSegment_056_0162_0009, g32p_row19_traceSegment_056_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 144 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 144 18 18, g32p_row19_traceSegment_056_0144_0018, g32p_row19_traceSegment_056_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 180 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 180 9 9, g32p_row19_traceSegment_056_0180_0009, g32p_row19_traceSegment_056_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 198 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 207 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 198 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 198 9 9, g32p_row19_traceSegment_056_0198_0009, g32p_row19_traceSegment_056_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 180 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 180 18 18, g32p_row19_traceSegment_056_0180_0018, g32p_row19_traceSegment_056_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 144 72 = [1, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 144 36 36, g32p_row19_traceSegment_056_0144_0036, g32p_row19_traceSegment_056_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 216 9 9, g32p_row19_traceSegment_056_0216_0009, g32p_row19_traceSegment_056_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 234 9 9, g32p_row19_traceSegment_056_0234_0009, g32p_row19_traceSegment_056_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 216 18 18, g32p_row19_traceSegment_056_0216_0018, g32p_row19_traceSegment_056_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 252 9 9, g32p_row19_traceSegment_056_0252_0009, g32p_row19_traceSegment_056_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 270 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 270 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 270 9 9, g32p_row19_traceSegment_056_0270_0009, g32p_row19_traceSegment_056_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 252 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 252 18 18, g32p_row19_traceSegment_056_0252_0018, g32p_row19_traceSegment_056_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 216 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 216 36 36, g32p_row19_traceSegment_056_0216_0036, g32p_row19_traceSegment_056_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 144 144 = [1, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 144 72 72, g32p_row19_traceSegment_056_0144_0072, g32p_row19_traceSegment_056_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_056 0 288 = [4, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 144 144, g32p_row19_traceSegment_056_0000_0144, g32p_row19_traceSegment_056_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 288 9 9, g32p_row19_traceSegment_056_0288_0009, g32p_row19_traceSegment_056_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 306 9 9, g32p_row19_traceSegment_056_0306_0009, g32p_row19_traceSegment_056_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 288 18 18, g32p_row19_traceSegment_056_0288_0018, g32p_row19_traceSegment_056_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 324 9 9, g32p_row19_traceSegment_056_0324_0009, g32p_row19_traceSegment_056_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 342 9 9, g32p_row19_traceSegment_056_0342_0009, g32p_row19_traceSegment_056_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 324 18 18, g32p_row19_traceSegment_056_0324_0018, g32p_row19_traceSegment_056_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 288 36 36, g32p_row19_traceSegment_056_0288_0036, g32p_row19_traceSegment_056_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 360 9 9, g32p_row19_traceSegment_056_0360_0009, g32p_row19_traceSegment_056_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 378 9 9, g32p_row19_traceSegment_056_0378_0009, g32p_row19_traceSegment_056_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 360 18 18, g32p_row19_traceSegment_056_0360_0018, g32p_row19_traceSegment_056_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 405 9 = [1, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 396 18 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 396 9 9, g32p_row19_traceSegment_056_0396_0009, g32p_row19_traceSegment_056_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 414 9 = [1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 414 18 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 414 9 9, g32p_row19_traceSegment_056_0414_0009, g32p_row19_traceSegment_056_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 396 36 = [2, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 396 18 18, g32p_row19_traceSegment_056_0396_0018, g32p_row19_traceSegment_056_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 360 72 = [2, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 360 36 36, g32p_row19_traceSegment_056_0360_0036, g32p_row19_traceSegment_056_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 288 144 = [2, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 288 72 72, g32p_row19_traceSegment_056_0288_0072, g32p_row19_traceSegment_056_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 432 9 = [1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 441 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 432 18 = [2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 432 9 9, g32p_row19_traceSegment_056_0432_0009, g32p_row19_traceSegment_056_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 450 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 450 9 9, g32p_row19_traceSegment_056_0450_0009, g32p_row19_traceSegment_056_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 432 36 = [3, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 432 18 18, g32p_row19_traceSegment_056_0432_0018, g32p_row19_traceSegment_056_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 468 9 9, g32p_row19_traceSegment_056_0468_0009, g32p_row19_traceSegment_056_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 486 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 486 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 486 9 9, g32p_row19_traceSegment_056_0486_0009, g32p_row19_traceSegment_056_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 468 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 468 18 18, g32p_row19_traceSegment_056_0468_0018, g32p_row19_traceSegment_056_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 432 72 = [3, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 432 36 36, g32p_row19_traceSegment_056_0432_0036, g32p_row19_traceSegment_056_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 504 9 = [1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 504 18 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 504 9 9, g32p_row19_traceSegment_056_0504_0009, g32p_row19_traceSegment_056_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 522 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 531 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 522 18 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 522 9 9, g32p_row19_traceSegment_056_0522_0009, g32p_row19_traceSegment_056_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 504 36 = [2, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 504 18 18, g32p_row19_traceSegment_056_0504_0018, g32p_row19_traceSegment_056_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 549 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 540 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 540 9 9, g32p_row19_traceSegment_056_0540_0009, g32p_row19_traceSegment_056_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 558 9 9, g32p_row19_traceSegment_056_0558_0009, g32p_row19_traceSegment_056_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 540 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 540 18 18, g32p_row19_traceSegment_056_0540_0018, g32p_row19_traceSegment_056_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 504 72 = [3, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 504 36 36, g32p_row19_traceSegment_056_0504_0036, g32p_row19_traceSegment_056_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 432 144 = [6, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 432 72 72, g32p_row19_traceSegment_056_0432_0072, g32p_row19_traceSegment_056_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_056 288 288 = [8, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 288 144 144, g32p_row19_traceSegment_056_0288_0144, g32p_row19_traceSegment_056_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_056 0 576 = [12, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 288 288, g32p_row19_traceSegment_056_0000_0288, g32p_row19_traceSegment_056_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 576 9 9, g32p_row19_traceSegment_056_0576_0009, g32p_row19_traceSegment_056_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 594 9 9, g32p_row19_traceSegment_056_0594_0009, g32p_row19_traceSegment_056_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 576 18 18, g32p_row19_traceSegment_056_0576_0018, g32p_row19_traceSegment_056_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 612 9 9, g32p_row19_traceSegment_056_0612_0009, g32p_row19_traceSegment_056_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 630 9 9, g32p_row19_traceSegment_056_0630_0009, g32p_row19_traceSegment_056_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 612 18 18, g32p_row19_traceSegment_056_0612_0018, g32p_row19_traceSegment_056_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 576 36 36, g32p_row19_traceSegment_056_0576_0036, g32p_row19_traceSegment_056_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 648 9 9, g32p_row19_traceSegment_056_0648_0009, g32p_row19_traceSegment_056_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 666 9 9, g32p_row19_traceSegment_056_0666_0009, g32p_row19_traceSegment_056_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 648 18 18, g32p_row19_traceSegment_056_0648_0018, g32p_row19_traceSegment_056_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 684 9 9, g32p_row19_traceSegment_056_0684_0009, g32p_row19_traceSegment_056_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 702 9 9, g32p_row19_traceSegment_056_0702_0009, g32p_row19_traceSegment_056_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 684 18 18, g32p_row19_traceSegment_056_0684_0018, g32p_row19_traceSegment_056_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 648 36 36, g32p_row19_traceSegment_056_0648_0036, g32p_row19_traceSegment_056_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 576 72 72, g32p_row19_traceSegment_056_0576_0072, g32p_row19_traceSegment_056_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 720 9 9, g32p_row19_traceSegment_056_0720_0009, g32p_row19_traceSegment_056_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 738 9 9, g32p_row19_traceSegment_056_0738_0009, g32p_row19_traceSegment_056_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 720 18 18, g32p_row19_traceSegment_056_0720_0018, g32p_row19_traceSegment_056_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 756 9 9, g32p_row19_traceSegment_056_0756_0009, g32p_row19_traceSegment_056_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 774 9 9, g32p_row19_traceSegment_056_0774_0009, g32p_row19_traceSegment_056_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 756 18 18, g32p_row19_traceSegment_056_0756_0018, g32p_row19_traceSegment_056_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 720 36 36, g32p_row19_traceSegment_056_0720_0036, g32p_row19_traceSegment_056_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 792 9 9, g32p_row19_traceSegment_056_0792_0009, g32p_row19_traceSegment_056_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 810 9 9, g32p_row19_traceSegment_056_0810_0009, g32p_row19_traceSegment_056_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 792 18 18, g32p_row19_traceSegment_056_0792_0018, g32p_row19_traceSegment_056_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 828 9 9, g32p_row19_traceSegment_056_0828_0009, g32p_row19_traceSegment_056_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 846 9 9, g32p_row19_traceSegment_056_0846_0009, g32p_row19_traceSegment_056_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 828 18 18, g32p_row19_traceSegment_056_0828_0018, g32p_row19_traceSegment_056_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 792 36 36, g32p_row19_traceSegment_056_0792_0036, g32p_row19_traceSegment_056_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 720 72 72, g32p_row19_traceSegment_056_0720_0072, g32p_row19_traceSegment_056_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_056 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 576 144 144, g32p_row19_traceSegment_056_0576_0144, g32p_row19_traceSegment_056_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 864 9 9, g32p_row19_traceSegment_056_0864_0009, g32p_row19_traceSegment_056_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 882 9 9, g32p_row19_traceSegment_056_0882_0009, g32p_row19_traceSegment_056_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 864 18 18, g32p_row19_traceSegment_056_0864_0018, g32p_row19_traceSegment_056_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 900 9 9, g32p_row19_traceSegment_056_0900_0009, g32p_row19_traceSegment_056_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 918 9 9, g32p_row19_traceSegment_056_0918_0009, g32p_row19_traceSegment_056_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 900 18 18, g32p_row19_traceSegment_056_0900_0018, g32p_row19_traceSegment_056_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 864 36 36, g32p_row19_traceSegment_056_0864_0036, g32p_row19_traceSegment_056_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 936 9 9, g32p_row19_traceSegment_056_0936_0009, g32p_row19_traceSegment_056_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 954 9 9, g32p_row19_traceSegment_056_0954_0009, g32p_row19_traceSegment_056_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 936 18 18, g32p_row19_traceSegment_056_0936_0018, g32p_row19_traceSegment_056_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 972 9 9, g32p_row19_traceSegment_056_0972_0009, g32p_row19_traceSegment_056_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 999 9 = [1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 990 18 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 990 9 9, g32p_row19_traceSegment_056_0990_0009, g32p_row19_traceSegment_056_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 972 36 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 972 18 18, g32p_row19_traceSegment_056_0972_0018, g32p_row19_traceSegment_056_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 936 72 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 936 36 36, g32p_row19_traceSegment_056_0936_0036, g32p_row19_traceSegment_056_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 864 144 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 864 72 72, g32p_row19_traceSegment_056_0864_0072, g32p_row19_traceSegment_056_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1008 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1017 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1008 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1008 9 9, g32p_row19_traceSegment_056_1008_0009, g32p_row19_traceSegment_056_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1026 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1026 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1026 9 9, g32p_row19_traceSegment_056_1026_0009, g32p_row19_traceSegment_056_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 1008 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1008 18 18, g32p_row19_traceSegment_056_1008_0018, g32p_row19_traceSegment_056_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1044 9 9, g32p_row19_traceSegment_056_1044_0009, g32p_row19_traceSegment_056_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1062 9 9, g32p_row19_traceSegment_056_1062_0009, g32p_row19_traceSegment_056_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1044 18 18, g32p_row19_traceSegment_056_1044_0018, g32p_row19_traceSegment_056_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 1008 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1008 36 36, g32p_row19_traceSegment_056_1008_0036, g32p_row19_traceSegment_056_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1080 9 9, g32p_row19_traceSegment_056_1080_0009, g32p_row19_traceSegment_056_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1098 9 9, g32p_row19_traceSegment_056_1098_0009, g32p_row19_traceSegment_056_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1080 18 18, g32p_row19_traceSegment_056_1080_0018, g32p_row19_traceSegment_056_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1116 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1116 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1116 9 9, g32p_row19_traceSegment_056_1116_0009, g32p_row19_traceSegment_056_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_056 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_056_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_056 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1134 9 9, g32p_row19_traceSegment_056_1134_0009, g32p_row19_traceSegment_056_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_056 1116 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1116 18 18, g32p_row19_traceSegment_056_1116_0018, g32p_row19_traceSegment_056_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_056 1080 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1080 36 36, g32p_row19_traceSegment_056_1080_0036, g32p_row19_traceSegment_056_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_056_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_056 1008 144 = [3, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 1008 72 72, g32p_row19_traceSegment_056_1008_0072, g32p_row19_traceSegment_056_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_056 864 288 = [4, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 864 144 144, g32p_row19_traceSegment_056_0864_0144, g32p_row19_traceSegment_056_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_056 576 576 = [4, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 576 288 288, g32p_row19_traceSegment_056_0576_0288, g32p_row19_traceSegment_056_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_056_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_056 0 1152 = [16, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_056 0 576 576, g32p_row19_traceSegment_056_0000_0576, g32p_row19_traceSegment_056_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 56 = [16, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_056_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_057_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 9 9, g32p_row19_traceSegment_057_0000_0009, g32p_row19_traceSegment_057_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 18 9 9, g32p_row19_traceSegment_057_0018_0009, g32p_row19_traceSegment_057_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 18 18, g32p_row19_traceSegment_057_0000_0018, g32p_row19_traceSegment_057_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 36 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 45 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 36 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 36 9 9, g32p_row19_traceSegment_057_0036_0009, g32p_row19_traceSegment_057_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 63 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 54 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 54 9 9, g32p_row19_traceSegment_057_0054_0009, g32p_row19_traceSegment_057_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 36 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 36 18 18, g32p_row19_traceSegment_057_0036_0018, g32p_row19_traceSegment_057_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 0 72 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 36 36, g32p_row19_traceSegment_057_0000_0036, g32p_row19_traceSegment_057_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 72 9 9, g32p_row19_traceSegment_057_0072_0009, g32p_row19_traceSegment_057_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 90 9 9, g32p_row19_traceSegment_057_0090_0009, g32p_row19_traceSegment_057_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 72 18 18, g32p_row19_traceSegment_057_0072_0018, g32p_row19_traceSegment_057_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 108 9 9, g32p_row19_traceSegment_057_0108_0009, g32p_row19_traceSegment_057_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 126 9 9, g32p_row19_traceSegment_057_0126_0009, g32p_row19_traceSegment_057_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 108 18 18, g32p_row19_traceSegment_057_0108_0018, g32p_row19_traceSegment_057_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 72 36 36, g32p_row19_traceSegment_057_0072_0036, g32p_row19_traceSegment_057_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 0 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 72 72, g32p_row19_traceSegment_057_0000_0072, g32p_row19_traceSegment_057_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 144 9 9, g32p_row19_traceSegment_057_0144_0009, g32p_row19_traceSegment_057_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 162 9 9, g32p_row19_traceSegment_057_0162_0009, g32p_row19_traceSegment_057_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 144 18 18, g32p_row19_traceSegment_057_0144_0018, g32p_row19_traceSegment_057_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 180 9 9, g32p_row19_traceSegment_057_0180_0009, g32p_row19_traceSegment_057_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 198 9 9, g32p_row19_traceSegment_057_0198_0009, g32p_row19_traceSegment_057_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 180 18 18, g32p_row19_traceSegment_057_0180_0018, g32p_row19_traceSegment_057_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 144 36 36, g32p_row19_traceSegment_057_0144_0036, g32p_row19_traceSegment_057_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 216 9 9, g32p_row19_traceSegment_057_0216_0009, g32p_row19_traceSegment_057_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 234 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 234 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 234 9 9, g32p_row19_traceSegment_057_0234_0009, g32p_row19_traceSegment_057_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 216 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 216 18 18, g32p_row19_traceSegment_057_0216_0018, g32p_row19_traceSegment_057_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 252 9 9, g32p_row19_traceSegment_057_0252_0009, g32p_row19_traceSegment_057_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 279 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 270 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 270 9 9, g32p_row19_traceSegment_057_0270_0009, g32p_row19_traceSegment_057_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 252 18 18, g32p_row19_traceSegment_057_0252_0018, g32p_row19_traceSegment_057_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 216 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 216 36 36, g32p_row19_traceSegment_057_0216_0036, g32p_row19_traceSegment_057_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 144 144 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 144 72 72, g32p_row19_traceSegment_057_0144_0072, g32p_row19_traceSegment_057_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_057 0 288 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 144 144, g32p_row19_traceSegment_057_0000_0144, g32p_row19_traceSegment_057_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 288 9 9, g32p_row19_traceSegment_057_0288_0009, g32p_row19_traceSegment_057_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 306 9 9, g32p_row19_traceSegment_057_0306_0009, g32p_row19_traceSegment_057_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 288 18 18, g32p_row19_traceSegment_057_0288_0018, g32p_row19_traceSegment_057_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 324 9 9, g32p_row19_traceSegment_057_0324_0009, g32p_row19_traceSegment_057_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 342 9 9, g32p_row19_traceSegment_057_0342_0009, g32p_row19_traceSegment_057_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 324 18 18, g32p_row19_traceSegment_057_0324_0018, g32p_row19_traceSegment_057_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 288 36 36, g32p_row19_traceSegment_057_0288_0036, g32p_row19_traceSegment_057_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 360 9 9, g32p_row19_traceSegment_057_0360_0009, g32p_row19_traceSegment_057_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 378 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 387 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 378 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 378 9 9, g32p_row19_traceSegment_057_0378_0009, g32p_row19_traceSegment_057_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 360 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 360 18 18, g32p_row19_traceSegment_057_0360_0018, g32p_row19_traceSegment_057_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 396 9 9, g32p_row19_traceSegment_057_0396_0009, g32p_row19_traceSegment_057_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 414 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 423 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 414 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 414 9 9, g32p_row19_traceSegment_057_0414_0009, g32p_row19_traceSegment_057_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 396 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 396 18 18, g32p_row19_traceSegment_057_0396_0018, g32p_row19_traceSegment_057_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 360 72 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 360 36 36, g32p_row19_traceSegment_057_0360_0036, g32p_row19_traceSegment_057_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 288 144 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 288 72 72, g32p_row19_traceSegment_057_0288_0072, g32p_row19_traceSegment_057_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 441 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 432 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 432 9 9, g32p_row19_traceSegment_057_0432_0009, g32p_row19_traceSegment_057_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 459 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 450 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 450 9 9, g32p_row19_traceSegment_057_0450_0009, g32p_row19_traceSegment_057_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 432 36 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 432 18 18, g32p_row19_traceSegment_057_0432_0018, g32p_row19_traceSegment_057_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 468 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 477 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 468 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 468 9 9, g32p_row19_traceSegment_057_0468_0009, g32p_row19_traceSegment_057_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 486 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 486 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 486 9 9, g32p_row19_traceSegment_057_0486_0009, g32p_row19_traceSegment_057_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 468 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 468 18 18, g32p_row19_traceSegment_057_0468_0018, g32p_row19_traceSegment_057_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 432 72 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 432 36 36, g32p_row19_traceSegment_057_0432_0036, g32p_row19_traceSegment_057_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 504 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 513 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 504 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 504 9 9, g32p_row19_traceSegment_057_0504_0009, g32p_row19_traceSegment_057_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 522 9 9, g32p_row19_traceSegment_057_0522_0009, g32p_row19_traceSegment_057_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 504 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 504 18 18, g32p_row19_traceSegment_057_0504_0018, g32p_row19_traceSegment_057_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 549 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 540 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 540 9 9, g32p_row19_traceSegment_057_0540_0009, g32p_row19_traceSegment_057_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 558 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 567 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 558 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 558 9 9, g32p_row19_traceSegment_057_0558_0009, g32p_row19_traceSegment_057_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 540 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 540 18 18, g32p_row19_traceSegment_057_0540_0018, g32p_row19_traceSegment_057_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 504 72 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 504 36 36, g32p_row19_traceSegment_057_0504_0036, g32p_row19_traceSegment_057_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 432 144 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 432 72 72, g32p_row19_traceSegment_057_0432_0072, g32p_row19_traceSegment_057_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_057 288 288 = [0, 25] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 288 144 144, g32p_row19_traceSegment_057_0288_0144, g32p_row19_traceSegment_057_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_057 0 576 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 288 288, g32p_row19_traceSegment_057_0000_0288, g32p_row19_traceSegment_057_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 576 9 9, g32p_row19_traceSegment_057_0576_0009, g32p_row19_traceSegment_057_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 594 9 9, g32p_row19_traceSegment_057_0594_0009, g32p_row19_traceSegment_057_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 576 18 18, g32p_row19_traceSegment_057_0576_0018, g32p_row19_traceSegment_057_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 612 9 9, g32p_row19_traceSegment_057_0612_0009, g32p_row19_traceSegment_057_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 630 9 9, g32p_row19_traceSegment_057_0630_0009, g32p_row19_traceSegment_057_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 612 18 18, g32p_row19_traceSegment_057_0612_0018, g32p_row19_traceSegment_057_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 576 36 36, g32p_row19_traceSegment_057_0576_0036, g32p_row19_traceSegment_057_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 648 9 9, g32p_row19_traceSegment_057_0648_0009, g32p_row19_traceSegment_057_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 666 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 675 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 666 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 666 9 9, g32p_row19_traceSegment_057_0666_0009, g32p_row19_traceSegment_057_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 648 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 648 18 18, g32p_row19_traceSegment_057_0648_0018, g32p_row19_traceSegment_057_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 684 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 693 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 684 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 684 9 9, g32p_row19_traceSegment_057_0684_0009, g32p_row19_traceSegment_057_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 711 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 702 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 702 9 9, g32p_row19_traceSegment_057_0702_0009, g32p_row19_traceSegment_057_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 684 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 684 18 18, g32p_row19_traceSegment_057_0684_0018, g32p_row19_traceSegment_057_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 648 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 648 36 36, g32p_row19_traceSegment_057_0648_0036, g32p_row19_traceSegment_057_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 576 144 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 576 72 72, g32p_row19_traceSegment_057_0576_0072, g32p_row19_traceSegment_057_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 720 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 720 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 720 9 9, g32p_row19_traceSegment_057_0720_0009, g32p_row19_traceSegment_057_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 738 9 9, g32p_row19_traceSegment_057_0738_0009, g32p_row19_traceSegment_057_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 720 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 720 18 18, g32p_row19_traceSegment_057_0720_0018, g32p_row19_traceSegment_057_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 756 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 765 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 756 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 756 9 9, g32p_row19_traceSegment_057_0756_0009, g32p_row19_traceSegment_057_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 774 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 774 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 774 9 9, g32p_row19_traceSegment_057_0774_0009, g32p_row19_traceSegment_057_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 756 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 756 18 18, g32p_row19_traceSegment_057_0756_0018, g32p_row19_traceSegment_057_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 720 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 720 36 36, g32p_row19_traceSegment_057_0720_0036, g32p_row19_traceSegment_057_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 792 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 792 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 792 9 9, g32p_row19_traceSegment_057_0792_0009, g32p_row19_traceSegment_057_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 810 9 9, g32p_row19_traceSegment_057_0810_0009, g32p_row19_traceSegment_057_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 792 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 792 18 18, g32p_row19_traceSegment_057_0792_0018, g32p_row19_traceSegment_057_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 828 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 828 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 828 9 9, g32p_row19_traceSegment_057_0828_0009, g32p_row19_traceSegment_057_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 846 9 9, g32p_row19_traceSegment_057_0846_0009, g32p_row19_traceSegment_057_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 828 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 828 18 18, g32p_row19_traceSegment_057_0828_0018, g32p_row19_traceSegment_057_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 792 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 792 36 36, g32p_row19_traceSegment_057_0792_0036, g32p_row19_traceSegment_057_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 720 144 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 720 72 72, g32p_row19_traceSegment_057_0720_0072, g32p_row19_traceSegment_057_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_057 576 288 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 576 144 144, g32p_row19_traceSegment_057_0576_0144, g32p_row19_traceSegment_057_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 864 9 9, g32p_row19_traceSegment_057_0864_0009, g32p_row19_traceSegment_057_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 882 9 9, g32p_row19_traceSegment_057_0882_0009, g32p_row19_traceSegment_057_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 864 18 18, g32p_row19_traceSegment_057_0864_0018, g32p_row19_traceSegment_057_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 900 9 9, g32p_row19_traceSegment_057_0900_0009, g32p_row19_traceSegment_057_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 918 9 9, g32p_row19_traceSegment_057_0918_0009, g32p_row19_traceSegment_057_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 900 18 18, g32p_row19_traceSegment_057_0900_0018, g32p_row19_traceSegment_057_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 864 36 36, g32p_row19_traceSegment_057_0864_0036, g32p_row19_traceSegment_057_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 936 9 9, g32p_row19_traceSegment_057_0936_0009, g32p_row19_traceSegment_057_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 954 9 9, g32p_row19_traceSegment_057_0954_0009, g32p_row19_traceSegment_057_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 936 18 18, g32p_row19_traceSegment_057_0936_0018, g32p_row19_traceSegment_057_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 972 9 9, g32p_row19_traceSegment_057_0972_0009, g32p_row19_traceSegment_057_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 990 9 9, g32p_row19_traceSegment_057_0990_0009, g32p_row19_traceSegment_057_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 972 18 18, g32p_row19_traceSegment_057_0972_0018, g32p_row19_traceSegment_057_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 936 36 36, g32p_row19_traceSegment_057_0936_0036, g32p_row19_traceSegment_057_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 864 72 72, g32p_row19_traceSegment_057_0864_0072, g32p_row19_traceSegment_057_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1008 9 9, g32p_row19_traceSegment_057_1008_0009, g32p_row19_traceSegment_057_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1035 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1026 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1026 9 9, g32p_row19_traceSegment_057_1026_0009, g32p_row19_traceSegment_057_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 1008 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1008 18 18, g32p_row19_traceSegment_057_1008_0018, g32p_row19_traceSegment_057_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1044 9 9, g32p_row19_traceSegment_057_1044_0009, g32p_row19_traceSegment_057_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1071 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1062 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1062 9 9, g32p_row19_traceSegment_057_1062_0009, g32p_row19_traceSegment_057_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 1044 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1044 18 18, g32p_row19_traceSegment_057_1044_0018, g32p_row19_traceSegment_057_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 1008 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1008 36 36, g32p_row19_traceSegment_057_1008_0036, g32p_row19_traceSegment_057_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1080 9 9, g32p_row19_traceSegment_057_1080_0009, g32p_row19_traceSegment_057_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1098 9 9, g32p_row19_traceSegment_057_1098_0009, g32p_row19_traceSegment_057_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1080 18 18, g32p_row19_traceSegment_057_1080_0018, g32p_row19_traceSegment_057_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1116 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1116 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1116 9 9, g32p_row19_traceSegment_057_1116_0009, g32p_row19_traceSegment_057_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_057 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_057_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_057 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1134 9 9, g32p_row19_traceSegment_057_1134_0009, g32p_row19_traceSegment_057_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_057 1116 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1116 18 18, g32p_row19_traceSegment_057_1116_0018, g32p_row19_traceSegment_057_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_057 1080 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1080 36 36, g32p_row19_traceSegment_057_1080_0036, g32p_row19_traceSegment_057_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_057_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_057 1008 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 1008 72 72, g32p_row19_traceSegment_057_1008_0072, g32p_row19_traceSegment_057_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_057 864 288 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 864 144 144, g32p_row19_traceSegment_057_0864_0144, g32p_row19_traceSegment_057_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_057 576 576 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 576 288 288, g32p_row19_traceSegment_057_0576_0288, g32p_row19_traceSegment_057_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_057_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_057 0 1152 = [0, 48] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_057 0 576 576, g32p_row19_traceSegment_057_0000_0576, g32p_row19_traceSegment_057_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 57 = [0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_057_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_059 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 59 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_059_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 9 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 0 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 9 9, g32p_row19_traceSegment_059_0000_0009, g32p_row19_traceSegment_059_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 18 9 9, g32p_row19_traceSegment_059_0018_0009, g32p_row19_traceSegment_059_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 0 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 18 18, g32p_row19_traceSegment_059_0000_0018, g32p_row19_traceSegment_059_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 36 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 45 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 36 18 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 36 9 9, g32p_row19_traceSegment_059_0036_0009, g32p_row19_traceSegment_059_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 63 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 54 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 54 9 9, g32p_row19_traceSegment_059_0054_0009, g32p_row19_traceSegment_059_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 36 36 = [0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 36 18 18, g32p_row19_traceSegment_059_0036_0018, g32p_row19_traceSegment_059_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 0 72 = [0, 0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 36 36, g32p_row19_traceSegment_059_0000_0036, g32p_row19_traceSegment_059_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 72 9 9, g32p_row19_traceSegment_059_0072_0009, g32p_row19_traceSegment_059_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 90 9 9, g32p_row19_traceSegment_059_0090_0009, g32p_row19_traceSegment_059_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 72 18 18, g32p_row19_traceSegment_059_0072_0018, g32p_row19_traceSegment_059_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 108 9 9, g32p_row19_traceSegment_059_0108_0009, g32p_row19_traceSegment_059_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 135 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 126 9 9, g32p_row19_traceSegment_059_0126_0009, g32p_row19_traceSegment_059_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 108 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 108 18 18, g32p_row19_traceSegment_059_0108_0018, g32p_row19_traceSegment_059_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 72 36 36, g32p_row19_traceSegment_059_0072_0036, g32p_row19_traceSegment_059_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 0 144 = [0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 72 72, g32p_row19_traceSegment_059_0000_0072, g32p_row19_traceSegment_059_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 144 9 9, g32p_row19_traceSegment_059_0144_0009, g32p_row19_traceSegment_059_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 162 9 9, g32p_row19_traceSegment_059_0162_0009, g32p_row19_traceSegment_059_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 144 18 18, g32p_row19_traceSegment_059_0144_0018, g32p_row19_traceSegment_059_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 180 9 9, g32p_row19_traceSegment_059_0180_0009, g32p_row19_traceSegment_059_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 198 9 9, g32p_row19_traceSegment_059_0198_0009, g32p_row19_traceSegment_059_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 180 18 18, g32p_row19_traceSegment_059_0180_0018, g32p_row19_traceSegment_059_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 144 36 36, g32p_row19_traceSegment_059_0144_0036, g32p_row19_traceSegment_059_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 225 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 216 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 216 9 9, g32p_row19_traceSegment_059_0216_0009, g32p_row19_traceSegment_059_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 243 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 234 9 9, g32p_row19_traceSegment_059_0234_0009, g32p_row19_traceSegment_059_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 216 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 216 18 18, g32p_row19_traceSegment_059_0216_0018, g32p_row19_traceSegment_059_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 252 9 9, g32p_row19_traceSegment_059_0252_0009, g32p_row19_traceSegment_059_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 279 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 270 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 270 9 9, g32p_row19_traceSegment_059_0270_0009, g32p_row19_traceSegment_059_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 252 18 18, g32p_row19_traceSegment_059_0252_0018, g32p_row19_traceSegment_059_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 216 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 216 36 36, g32p_row19_traceSegment_059_0216_0036, g32p_row19_traceSegment_059_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 144 144 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 144 72 72, g32p_row19_traceSegment_059_0144_0072, g32p_row19_traceSegment_059_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_059 0 288 = [0, 0, 4, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 144 144, g32p_row19_traceSegment_059_0000_0144, g32p_row19_traceSegment_059_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 288 9 9, g32p_row19_traceSegment_059_0288_0009, g32p_row19_traceSegment_059_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 306 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 306 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 306 9 9, g32p_row19_traceSegment_059_0306_0009, g32p_row19_traceSegment_059_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 288 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 288 18 18, g32p_row19_traceSegment_059_0288_0018, g32p_row19_traceSegment_059_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 324 9 9, g32p_row19_traceSegment_059_0324_0009, g32p_row19_traceSegment_059_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 342 9 9, g32p_row19_traceSegment_059_0342_0009, g32p_row19_traceSegment_059_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 324 18 18, g32p_row19_traceSegment_059_0324_0018, g32p_row19_traceSegment_059_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 288 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 288 36 36, g32p_row19_traceSegment_059_0288_0036, g32p_row19_traceSegment_059_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 360 9 9, g32p_row19_traceSegment_059_0360_0009, g32p_row19_traceSegment_059_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 378 9 9, g32p_row19_traceSegment_059_0378_0009, g32p_row19_traceSegment_059_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 360 18 18, g32p_row19_traceSegment_059_0360_0018, g32p_row19_traceSegment_059_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 405 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 396 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 396 9 9, g32p_row19_traceSegment_059_0396_0009, g32p_row19_traceSegment_059_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 423 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 414 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 414 9 9, g32p_row19_traceSegment_059_0414_0009, g32p_row19_traceSegment_059_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 396 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 396 18 18, g32p_row19_traceSegment_059_0396_0018, g32p_row19_traceSegment_059_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 360 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 360 36 36, g32p_row19_traceSegment_059_0360_0036, g32p_row19_traceSegment_059_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 288 144 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 288 72 72, g32p_row19_traceSegment_059_0288_0072, g32p_row19_traceSegment_059_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 432 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 432 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 432 9 9, g32p_row19_traceSegment_059_0432_0009, g32p_row19_traceSegment_059_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 450 9 9, g32p_row19_traceSegment_059_0450_0009, g32p_row19_traceSegment_059_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 432 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 432 18 18, g32p_row19_traceSegment_059_0432_0018, g32p_row19_traceSegment_059_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 468 9 9, g32p_row19_traceSegment_059_0468_0009, g32p_row19_traceSegment_059_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 486 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 495 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 486 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 486 9 9, g32p_row19_traceSegment_059_0486_0009, g32p_row19_traceSegment_059_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 468 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 468 18 18, g32p_row19_traceSegment_059_0468_0018, g32p_row19_traceSegment_059_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 432 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 432 36 36, g32p_row19_traceSegment_059_0432_0036, g32p_row19_traceSegment_059_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 513 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 504 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 504 9 9, g32p_row19_traceSegment_059_0504_0009, g32p_row19_traceSegment_059_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 522 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 522 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 522 9 9, g32p_row19_traceSegment_059_0522_0009, g32p_row19_traceSegment_059_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 504 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 504 18 18, g32p_row19_traceSegment_059_0504_0018, g32p_row19_traceSegment_059_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 540 9 9, g32p_row19_traceSegment_059_0540_0009, g32p_row19_traceSegment_059_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 567 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 558 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 558 9 9, g32p_row19_traceSegment_059_0558_0009, g32p_row19_traceSegment_059_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 540 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 540 18 18, g32p_row19_traceSegment_059_0540_0018, g32p_row19_traceSegment_059_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 504 72 = [0, 0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 504 36 36, g32p_row19_traceSegment_059_0504_0036, g32p_row19_traceSegment_059_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 432 144 = [0, 0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 432 72 72, g32p_row19_traceSegment_059_0432_0072, g32p_row19_traceSegment_059_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_059 288 288 = [0, 0, 1, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 288 144 144, g32p_row19_traceSegment_059_0288_0144, g32p_row19_traceSegment_059_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_059 0 576 = [0, 0, 5, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 288 288, g32p_row19_traceSegment_059_0000_0288, g32p_row19_traceSegment_059_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 576 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 585 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 576 18 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 576 9 9, g32p_row19_traceSegment_059_0576_0009, g32p_row19_traceSegment_059_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 603 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 594 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 594 9 9, g32p_row19_traceSegment_059_0594_0009, g32p_row19_traceSegment_059_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 576 36 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 576 18 18, g32p_row19_traceSegment_059_0576_0018, g32p_row19_traceSegment_059_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 612 9 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 621 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 612 18 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 612 9 9, g32p_row19_traceSegment_059_0612_0009, g32p_row19_traceSegment_059_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 630 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 639 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 630 18 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 630 9 9, g32p_row19_traceSegment_059_0630_0009, g32p_row19_traceSegment_059_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 612 36 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 612 18 18, g32p_row19_traceSegment_059_0612_0018, g32p_row19_traceSegment_059_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 576 72 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 576 36 36, g32p_row19_traceSegment_059_0576_0036, g32p_row19_traceSegment_059_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 648 9 9, g32p_row19_traceSegment_059_0648_0009, g32p_row19_traceSegment_059_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 666 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 675 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 666 18 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 666 9 9, g32p_row19_traceSegment_059_0666_0009, g32p_row19_traceSegment_059_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 648 36 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 648 18 18, g32p_row19_traceSegment_059_0648_0018, g32p_row19_traceSegment_059_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 684 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 693 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 684 18 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 684 9 9, g32p_row19_traceSegment_059_0684_0009, g32p_row19_traceSegment_059_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 711 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 702 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 702 9 9, g32p_row19_traceSegment_059_0702_0009, g32p_row19_traceSegment_059_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 684 36 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 684 18 18, g32p_row19_traceSegment_059_0684_0018, g32p_row19_traceSegment_059_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 648 72 = [0, 0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 648 36 36, g32p_row19_traceSegment_059_0648_0036, g32p_row19_traceSegment_059_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 576 144 = [0, 0, 18, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 576 72 72, g32p_row19_traceSegment_059_0576_0072, g32p_row19_traceSegment_059_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 720 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 729 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 720 18 = [0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 720 9 9, g32p_row19_traceSegment_059_0720_0009, g32p_row19_traceSegment_059_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 738 9 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 747 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 738 18 = [0, 0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 738 9 9, g32p_row19_traceSegment_059_0738_0009, g32p_row19_traceSegment_059_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 720 36 = [0, 0, 7, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 720 18 18, g32p_row19_traceSegment_059_0720_0018, g32p_row19_traceSegment_059_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 756 9 9, g32p_row19_traceSegment_059_0756_0009, g32p_row19_traceSegment_059_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 783 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 774 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 774 9 9, g32p_row19_traceSegment_059_0774_0009, g32p_row19_traceSegment_059_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 756 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 756 18 18, g32p_row19_traceSegment_059_0756_0018, g32p_row19_traceSegment_059_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 720 72 = [0, 0, 7, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 720 36 36, g32p_row19_traceSegment_059_0720_0036, g32p_row19_traceSegment_059_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 792 9 9, g32p_row19_traceSegment_059_0792_0009, g32p_row19_traceSegment_059_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 819 9 = [0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 810 18 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 810 9 9, g32p_row19_traceSegment_059_0810_0009, g32p_row19_traceSegment_059_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 792 36 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 792 18 18, g32p_row19_traceSegment_059_0792_0018, g32p_row19_traceSegment_059_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 828 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 837 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 828 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 828 9 9, g32p_row19_traceSegment_059_0828_0009, g32p_row19_traceSegment_059_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 846 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 846 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 846 9 9, g32p_row19_traceSegment_059_0846_0009, g32p_row19_traceSegment_059_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 828 36 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 828 18 18, g32p_row19_traceSegment_059_0828_0018, g32p_row19_traceSegment_059_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 792 72 = [0, 0, 1, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 792 36 36, g32p_row19_traceSegment_059_0792_0036, g32p_row19_traceSegment_059_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 720 144 = [0, 0, 8, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 720 72 72, g32p_row19_traceSegment_059_0720_0072, g32p_row19_traceSegment_059_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_059 576 288 = [0, 0, 26, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 576 144 144, g32p_row19_traceSegment_059_0576_0144, g32p_row19_traceSegment_059_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 873 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 864 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 864 9 9, g32p_row19_traceSegment_059_0864_0009, g32p_row19_traceSegment_059_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 882 9 9, g32p_row19_traceSegment_059_0882_0009, g32p_row19_traceSegment_059_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 864 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 864 18 18, g32p_row19_traceSegment_059_0864_0018, g32p_row19_traceSegment_059_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 900 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 900 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 900 9 9, g32p_row19_traceSegment_059_0900_0009, g32p_row19_traceSegment_059_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 918 9 9, g32p_row19_traceSegment_059_0918_0009, g32p_row19_traceSegment_059_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 900 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 900 18 18, g32p_row19_traceSegment_059_0900_0018, g32p_row19_traceSegment_059_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 864 72 = [0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 864 36 36, g32p_row19_traceSegment_059_0864_0036, g32p_row19_traceSegment_059_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 936 9 9, g32p_row19_traceSegment_059_0936_0009, g32p_row19_traceSegment_059_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 954 9 9, g32p_row19_traceSegment_059_0954_0009, g32p_row19_traceSegment_059_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 936 18 18, g32p_row19_traceSegment_059_0936_0018, g32p_row19_traceSegment_059_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 972 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 972 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 972 9 9, g32p_row19_traceSegment_059_0972_0009, g32p_row19_traceSegment_059_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 990 9 9, g32p_row19_traceSegment_059_0990_0009, g32p_row19_traceSegment_059_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 972 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 972 18 18, g32p_row19_traceSegment_059_0972_0018, g32p_row19_traceSegment_059_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 936 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 936 36 36, g32p_row19_traceSegment_059_0936_0036, g32p_row19_traceSegment_059_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 864 144 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 864 72 72, g32p_row19_traceSegment_059_0864_0072, g32p_row19_traceSegment_059_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1008 9 9, g32p_row19_traceSegment_059_1008_0009, g32p_row19_traceSegment_059_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1026 9 9, g32p_row19_traceSegment_059_1026_0009, g32p_row19_traceSegment_059_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1008 18 18, g32p_row19_traceSegment_059_1008_0018, g32p_row19_traceSegment_059_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1044 9 9, g32p_row19_traceSegment_059_1044_0009, g32p_row19_traceSegment_059_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1062 9 9, g32p_row19_traceSegment_059_1062_0009, g32p_row19_traceSegment_059_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1044 18 18, g32p_row19_traceSegment_059_1044_0018, g32p_row19_traceSegment_059_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1008 36 36, g32p_row19_traceSegment_059_1008_0036, g32p_row19_traceSegment_059_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1080 9 9, g32p_row19_traceSegment_059_1080_0009, g32p_row19_traceSegment_059_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1098 9 9, g32p_row19_traceSegment_059_1098_0009, g32p_row19_traceSegment_059_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1080 18 18, g32p_row19_traceSegment_059_1080_0018, g32p_row19_traceSegment_059_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1116 9 9, g32p_row19_traceSegment_059_1116_0009, g32p_row19_traceSegment_059_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_059 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_059_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_059 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1134 9 9, g32p_row19_traceSegment_059_1134_0009, g32p_row19_traceSegment_059_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_059 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1116 18 18, g32p_row19_traceSegment_059_1116_0018, g32p_row19_traceSegment_059_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_059 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1080 36 36, g32p_row19_traceSegment_059_1080_0036, g32p_row19_traceSegment_059_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_059_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_059 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 1008 72 72, g32p_row19_traceSegment_059_1008_0072, g32p_row19_traceSegment_059_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_059 864 288 = [0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 864 144 144, g32p_row19_traceSegment_059_0864_0144, g32p_row19_traceSegment_059_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_059 576 576 = [0, 0, 27, 18] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 576 288 288, g32p_row19_traceSegment_059_0576_0288, g32p_row19_traceSegment_059_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_059_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_059 0 1152 = [0, 0, 32, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_059 0 576 576, g32p_row19_traceSegment_059_0000_0576, g32p_row19_traceSegment_059_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 59 = [0, 0, 32, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_059_0000_1152

end HodgeLean.Foundations.Program

end
end
