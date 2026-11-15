import HodgeLean.Foundations.Program.G32PropFourSixPacked0393
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_018_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 0 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 9 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 0 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 9 9, g32p_row24_traceSegment_018_0000_0009, g32p_row24_traceSegment_018_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 18 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 18 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 18 9 9, g32p_row24_traceSegment_018_0018_0009, g32p_row24_traceSegment_018_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 0 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 18 18, g32p_row24_traceSegment_018_0000_0018, g32p_row24_traceSegment_018_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 36 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 45 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 36 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 36 9 9, g32p_row24_traceSegment_018_0036_0009, g32p_row24_traceSegment_018_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 54 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 54 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 54 9 9, g32p_row24_traceSegment_018_0054_0009, g32p_row24_traceSegment_018_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 36 36 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 36 18 18, g32p_row24_traceSegment_018_0036_0018, g32p_row24_traceSegment_018_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 0 72 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 36 36, g32p_row24_traceSegment_018_0000_0036, g32p_row24_traceSegment_018_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 72 9 9, g32p_row24_traceSegment_018_0072_0009, g32p_row24_traceSegment_018_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 90 9 9, g32p_row24_traceSegment_018_0090_0009, g32p_row24_traceSegment_018_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 72 18 18, g32p_row24_traceSegment_018_0072_0018, g32p_row24_traceSegment_018_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 108 9 9, g32p_row24_traceSegment_018_0108_0009, g32p_row24_traceSegment_018_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 126 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 126 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 126 9 9, g32p_row24_traceSegment_018_0126_0009, g32p_row24_traceSegment_018_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 108 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 108 18 18, g32p_row24_traceSegment_018_0108_0018, g32p_row24_traceSegment_018_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 72 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 72 36 36, g32p_row24_traceSegment_018_0072_0036, g32p_row24_traceSegment_018_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 0 144 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 72 72, g32p_row24_traceSegment_018_0000_0072, g32p_row24_traceSegment_018_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 144 9 9, g32p_row24_traceSegment_018_0144_0009, g32p_row24_traceSegment_018_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 162 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 162 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 162 9 9, g32p_row24_traceSegment_018_0162_0009, g32p_row24_traceSegment_018_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 144 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 144 18 18, g32p_row24_traceSegment_018_0144_0018, g32p_row24_traceSegment_018_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 180 9 9, g32p_row24_traceSegment_018_0180_0009, g32p_row24_traceSegment_018_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 198 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 198 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 198 9 9, g32p_row24_traceSegment_018_0198_0009, g32p_row24_traceSegment_018_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 180 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 180 18 18, g32p_row24_traceSegment_018_0180_0018, g32p_row24_traceSegment_018_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 144 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 144 36 36, g32p_row24_traceSegment_018_0144_0036, g32p_row24_traceSegment_018_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 216 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 216 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 216 9 9, g32p_row24_traceSegment_018_0216_0009, g32p_row24_traceSegment_018_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 234 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 234 9 9, g32p_row24_traceSegment_018_0234_0009, g32p_row24_traceSegment_018_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 216 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 216 18 18, g32p_row24_traceSegment_018_0216_0018, g32p_row24_traceSegment_018_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 252 9 9, g32p_row24_traceSegment_018_0252_0009, g32p_row24_traceSegment_018_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 270 9 9, g32p_row24_traceSegment_018_0270_0009, g32p_row24_traceSegment_018_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 252 18 18, g32p_row24_traceSegment_018_0252_0018, g32p_row24_traceSegment_018_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 216 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 216 36 36, g32p_row24_traceSegment_018_0216_0036, g32p_row24_traceSegment_018_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 144 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 144 72 72, g32p_row24_traceSegment_018_0144_0072, g32p_row24_traceSegment_018_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_018 0 288 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 144 144, g32p_row24_traceSegment_018_0000_0144, g32p_row24_traceSegment_018_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 288 9 9, g32p_row24_traceSegment_018_0288_0009, g32p_row24_traceSegment_018_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 306 9 9, g32p_row24_traceSegment_018_0306_0009, g32p_row24_traceSegment_018_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 288 18 18, g32p_row24_traceSegment_018_0288_0018, g32p_row24_traceSegment_018_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 333 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 324 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 324 9 9, g32p_row24_traceSegment_018_0324_0009, g32p_row24_traceSegment_018_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 342 9 9, g32p_row24_traceSegment_018_0342_0009, g32p_row24_traceSegment_018_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 324 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 324 18 18, g32p_row24_traceSegment_018_0324_0018, g32p_row24_traceSegment_018_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 288 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 288 36 36, g32p_row24_traceSegment_018_0288_0036, g32p_row24_traceSegment_018_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 360 9 9, g32p_row24_traceSegment_018_0360_0009, g32p_row24_traceSegment_018_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 378 9 9, g32p_row24_traceSegment_018_0378_0009, g32p_row24_traceSegment_018_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 360 18 18, g32p_row24_traceSegment_018_0360_0018, g32p_row24_traceSegment_018_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 396 9 9, g32p_row24_traceSegment_018_0396_0009, g32p_row24_traceSegment_018_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 414 9 9, g32p_row24_traceSegment_018_0414_0009, g32p_row24_traceSegment_018_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 396 18 18, g32p_row24_traceSegment_018_0396_0018, g32p_row24_traceSegment_018_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 360 36 36, g32p_row24_traceSegment_018_0360_0036, g32p_row24_traceSegment_018_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 288 144 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 288 72 72, g32p_row24_traceSegment_018_0288_0072, g32p_row24_traceSegment_018_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 432 9 9, g32p_row24_traceSegment_018_0432_0009, g32p_row24_traceSegment_018_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 450 9 9, g32p_row24_traceSegment_018_0450_0009, g32p_row24_traceSegment_018_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 432 18 18, g32p_row24_traceSegment_018_0432_0018, g32p_row24_traceSegment_018_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 468 9 9, g32p_row24_traceSegment_018_0468_0009, g32p_row24_traceSegment_018_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 486 9 9, g32p_row24_traceSegment_018_0486_0009, g32p_row24_traceSegment_018_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 468 18 18, g32p_row24_traceSegment_018_0468_0018, g32p_row24_traceSegment_018_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 432 36 36, g32p_row24_traceSegment_018_0432_0036, g32p_row24_traceSegment_018_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 513 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 504 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 504 9 9, g32p_row24_traceSegment_018_0504_0009, g32p_row24_traceSegment_018_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 522 9 9, g32p_row24_traceSegment_018_0522_0009, g32p_row24_traceSegment_018_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 504 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 504 18 18, g32p_row24_traceSegment_018_0504_0018, g32p_row24_traceSegment_018_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 540 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 540 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 540 9 9, g32p_row24_traceSegment_018_0540_0009, g32p_row24_traceSegment_018_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 558 9 9, g32p_row24_traceSegment_018_0558_0009, g32p_row24_traceSegment_018_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 540 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 540 18 18, g32p_row24_traceSegment_018_0540_0018, g32p_row24_traceSegment_018_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 504 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 504 36 36, g32p_row24_traceSegment_018_0504_0036, g32p_row24_traceSegment_018_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 432 144 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 432 72 72, g32p_row24_traceSegment_018_0432_0072, g32p_row24_traceSegment_018_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_018 288 288 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 288 144 144, g32p_row24_traceSegment_018_0288_0144, g32p_row24_traceSegment_018_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_018 0 576 = [0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 288 288, g32p_row24_traceSegment_018_0000_0288, g32p_row24_traceSegment_018_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 576 9 9, g32p_row24_traceSegment_018_0576_0009, g32p_row24_traceSegment_018_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 594 9 9, g32p_row24_traceSegment_018_0594_0009, g32p_row24_traceSegment_018_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 576 18 18, g32p_row24_traceSegment_018_0576_0018, g32p_row24_traceSegment_018_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 621 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 612 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 612 9 9, g32p_row24_traceSegment_018_0612_0009, g32p_row24_traceSegment_018_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 630 9 9, g32p_row24_traceSegment_018_0630_0009, g32p_row24_traceSegment_018_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 612 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 612 18 18, g32p_row24_traceSegment_018_0612_0018, g32p_row24_traceSegment_018_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 576 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 576 36 36, g32p_row24_traceSegment_018_0576_0036, g32p_row24_traceSegment_018_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 648 9 9, g32p_row24_traceSegment_018_0648_0009, g32p_row24_traceSegment_018_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 666 9 9, g32p_row24_traceSegment_018_0666_0009, g32p_row24_traceSegment_018_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 648 18 18, g32p_row24_traceSegment_018_0648_0018, g32p_row24_traceSegment_018_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 684 9 9, g32p_row24_traceSegment_018_0684_0009, g32p_row24_traceSegment_018_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 702 9 9, g32p_row24_traceSegment_018_0702_0009, g32p_row24_traceSegment_018_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 684 18 18, g32p_row24_traceSegment_018_0684_0018, g32p_row24_traceSegment_018_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 648 36 36, g32p_row24_traceSegment_018_0648_0036, g32p_row24_traceSegment_018_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 576 144 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 576 72 72, g32p_row24_traceSegment_018_0576_0072, g32p_row24_traceSegment_018_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 729 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 720 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 720 9 9, g32p_row24_traceSegment_018_0720_0009, g32p_row24_traceSegment_018_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 738 9 9, g32p_row24_traceSegment_018_0738_0009, g32p_row24_traceSegment_018_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 720 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 720 18 18, g32p_row24_traceSegment_018_0720_0018, g32p_row24_traceSegment_018_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 756 9 9, g32p_row24_traceSegment_018_0756_0009, g32p_row24_traceSegment_018_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 774 9 9, g32p_row24_traceSegment_018_0774_0009, g32p_row24_traceSegment_018_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 756 18 18, g32p_row24_traceSegment_018_0756_0018, g32p_row24_traceSegment_018_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 720 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 720 36 36, g32p_row24_traceSegment_018_0720_0036, g32p_row24_traceSegment_018_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 792 9 9, g32p_row24_traceSegment_018_0792_0009, g32p_row24_traceSegment_018_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 810 9 9, g32p_row24_traceSegment_018_0810_0009, g32p_row24_traceSegment_018_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 792 18 18, g32p_row24_traceSegment_018_0792_0018, g32p_row24_traceSegment_018_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 828 9 9, g32p_row24_traceSegment_018_0828_0009, g32p_row24_traceSegment_018_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 846 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 846 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 846 9 9, g32p_row24_traceSegment_018_0846_0009, g32p_row24_traceSegment_018_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 828 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 828 18 18, g32p_row24_traceSegment_018_0828_0018, g32p_row24_traceSegment_018_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 792 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 792 36 36, g32p_row24_traceSegment_018_0792_0036, g32p_row24_traceSegment_018_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 720 144 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 720 72 72, g32p_row24_traceSegment_018_0720_0072, g32p_row24_traceSegment_018_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_018 576 288 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 576 144 144, g32p_row24_traceSegment_018_0576_0144, g32p_row24_traceSegment_018_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 864 9 9, g32p_row24_traceSegment_018_0864_0009, g32p_row24_traceSegment_018_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 891 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 882 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 882 9 9, g32p_row24_traceSegment_018_0882_0009, g32p_row24_traceSegment_018_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 864 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 864 18 18, g32p_row24_traceSegment_018_0864_0018, g32p_row24_traceSegment_018_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 900 9 9, g32p_row24_traceSegment_018_0900_0009, g32p_row24_traceSegment_018_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 918 9 9, g32p_row24_traceSegment_018_0918_0009, g32p_row24_traceSegment_018_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 900 18 18, g32p_row24_traceSegment_018_0900_0018, g32p_row24_traceSegment_018_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 864 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 864 36 36, g32p_row24_traceSegment_018_0864_0036, g32p_row24_traceSegment_018_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 936 9 9, g32p_row24_traceSegment_018_0936_0009, g32p_row24_traceSegment_018_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 954 9 9, g32p_row24_traceSegment_018_0954_0009, g32p_row24_traceSegment_018_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 936 18 18, g32p_row24_traceSegment_018_0936_0018, g32p_row24_traceSegment_018_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 972 9 9, g32p_row24_traceSegment_018_0972_0009, g32p_row24_traceSegment_018_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 990 9 9, g32p_row24_traceSegment_018_0990_0009, g32p_row24_traceSegment_018_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 972 18 18, g32p_row24_traceSegment_018_0972_0018, g32p_row24_traceSegment_018_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 936 36 36, g32p_row24_traceSegment_018_0936_0036, g32p_row24_traceSegment_018_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 864 144 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 864 72 72, g32p_row24_traceSegment_018_0864_0072, g32p_row24_traceSegment_018_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1008 9 9, g32p_row24_traceSegment_018_1008_0009, g32p_row24_traceSegment_018_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1035 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1026 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1026 9 9, g32p_row24_traceSegment_018_1026_0009, g32p_row24_traceSegment_018_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 1008 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1008 18 18, g32p_row24_traceSegment_018_1008_0018, g32p_row24_traceSegment_018_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1044 9 9, g32p_row24_traceSegment_018_1044_0009, g32p_row24_traceSegment_018_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1062 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1062 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1062 9 9, g32p_row24_traceSegment_018_1062_0009, g32p_row24_traceSegment_018_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 1044 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1044 18 18, g32p_row24_traceSegment_018_1044_0018, g32p_row24_traceSegment_018_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 1008 72 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1008 36 36, g32p_row24_traceSegment_018_1008_0036, g32p_row24_traceSegment_018_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1080 9 9, g32p_row24_traceSegment_018_1080_0009, g32p_row24_traceSegment_018_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1098 9 9, g32p_row24_traceSegment_018_1098_0009, g32p_row24_traceSegment_018_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1080 18 18, g32p_row24_traceSegment_018_1080_0018, g32p_row24_traceSegment_018_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1125 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1116 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1116 9 9, g32p_row24_traceSegment_018_1116_0009, g32p_row24_traceSegment_018_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1134 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_018 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_018_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_018 1134 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1134 9 9, g32p_row24_traceSegment_018_1134_0009, g32p_row24_traceSegment_018_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_018 1116 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1116 18 18, g32p_row24_traceSegment_018_1116_0018, g32p_row24_traceSegment_018_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_018 1080 72 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1080 36 36, g32p_row24_traceSegment_018_1080_0036, g32p_row24_traceSegment_018_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_018_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_018 1008 144 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 1008 72 72, g32p_row24_traceSegment_018_1008_0072, g32p_row24_traceSegment_018_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_018 864 288 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 864 144 144, g32p_row24_traceSegment_018_0864_0144, g32p_row24_traceSegment_018_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_018 576 576 = [2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 576 288 288, g32p_row24_traceSegment_018_0576_0288, g32p_row24_traceSegment_018_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_018_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_018 0 1152 = [2, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_018 0 576 576, g32p_row24_traceSegment_018_0000_0576, g32p_row24_traceSegment_018_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 18 = [2, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_018_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_031 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 31 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_031_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 9 9, g32p_row24_traceSegment_031_0000_0009, g32p_row24_traceSegment_031_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 18 9 9, g32p_row24_traceSegment_031_0018_0009, g32p_row24_traceSegment_031_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 18 18, g32p_row24_traceSegment_031_0000_0018, g32p_row24_traceSegment_031_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 36 9 9, g32p_row24_traceSegment_031_0036_0009, g32p_row24_traceSegment_031_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 54 9 9, g32p_row24_traceSegment_031_0054_0009, g32p_row24_traceSegment_031_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 36 18 18, g32p_row24_traceSegment_031_0036_0018, g32p_row24_traceSegment_031_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 36 36, g32p_row24_traceSegment_031_0000_0036, g32p_row24_traceSegment_031_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 81 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 72 9 9, g32p_row24_traceSegment_031_0072_0009, g32p_row24_traceSegment_031_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 90 9 9, g32p_row24_traceSegment_031_0090_0009, g32p_row24_traceSegment_031_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 72 18 18, g32p_row24_traceSegment_031_0072_0018, g32p_row24_traceSegment_031_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 108 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 108 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 108 9 9, g32p_row24_traceSegment_031_0108_0009, g32p_row24_traceSegment_031_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 126 9 9, g32p_row24_traceSegment_031_0126_0009, g32p_row24_traceSegment_031_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 108 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 108 18 18, g32p_row24_traceSegment_031_0108_0018, g32p_row24_traceSegment_031_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 72 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 72 36 36, g32p_row24_traceSegment_031_0072_0036, g32p_row24_traceSegment_031_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 72 72, g32p_row24_traceSegment_031_0000_0072, g32p_row24_traceSegment_031_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 144 9 9, g32p_row24_traceSegment_031_0144_0009, g32p_row24_traceSegment_031_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 162 9 9, g32p_row24_traceSegment_031_0162_0009, g32p_row24_traceSegment_031_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 144 18 18, g32p_row24_traceSegment_031_0144_0018, g32p_row24_traceSegment_031_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 180 9 9, g32p_row24_traceSegment_031_0180_0009, g32p_row24_traceSegment_031_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 198 9 9, g32p_row24_traceSegment_031_0198_0009, g32p_row24_traceSegment_031_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 180 18 18, g32p_row24_traceSegment_031_0180_0018, g32p_row24_traceSegment_031_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 144 36 36, g32p_row24_traceSegment_031_0144_0036, g32p_row24_traceSegment_031_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 216 9 9, g32p_row24_traceSegment_031_0216_0009, g32p_row24_traceSegment_031_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 234 9 9, g32p_row24_traceSegment_031_0234_0009, g32p_row24_traceSegment_031_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 216 18 18, g32p_row24_traceSegment_031_0216_0018, g32p_row24_traceSegment_031_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 252 9 9, g32p_row24_traceSegment_031_0252_0009, g32p_row24_traceSegment_031_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 270 9 9, g32p_row24_traceSegment_031_0270_0009, g32p_row24_traceSegment_031_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 252 18 18, g32p_row24_traceSegment_031_0252_0018, g32p_row24_traceSegment_031_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 216 36 36, g32p_row24_traceSegment_031_0216_0036, g32p_row24_traceSegment_031_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 144 72 72, g32p_row24_traceSegment_031_0144_0072, g32p_row24_traceSegment_031_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_031 0 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 144 144, g32p_row24_traceSegment_031_0000_0144, g32p_row24_traceSegment_031_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 297 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 288 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 288 9 9, g32p_row24_traceSegment_031_0288_0009, g32p_row24_traceSegment_031_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 306 9 9, g32p_row24_traceSegment_031_0306_0009, g32p_row24_traceSegment_031_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 288 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 288 18 18, g32p_row24_traceSegment_031_0288_0018, g32p_row24_traceSegment_031_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 324 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 324 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 324 9 9, g32p_row24_traceSegment_031_0324_0009, g32p_row24_traceSegment_031_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 342 9 9, g32p_row24_traceSegment_031_0342_0009, g32p_row24_traceSegment_031_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 324 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 324 18 18, g32p_row24_traceSegment_031_0324_0018, g32p_row24_traceSegment_031_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 288 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 288 36 36, g32p_row24_traceSegment_031_0288_0036, g32p_row24_traceSegment_031_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 360 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 360 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 360 9 9, g32p_row24_traceSegment_031_0360_0009, g32p_row24_traceSegment_031_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 378 9 9, g32p_row24_traceSegment_031_0378_0009, g32p_row24_traceSegment_031_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 360 18 18, g32p_row24_traceSegment_031_0360_0018, g32p_row24_traceSegment_031_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 396 9 9, g32p_row24_traceSegment_031_0396_0009, g32p_row24_traceSegment_031_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 414 9 9, g32p_row24_traceSegment_031_0414_0009, g32p_row24_traceSegment_031_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 396 18 18, g32p_row24_traceSegment_031_0396_0018, g32p_row24_traceSegment_031_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 360 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 360 36 36, g32p_row24_traceSegment_031_0360_0036, g32p_row24_traceSegment_031_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 288 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 288 72 72, g32p_row24_traceSegment_031_0288_0072, g32p_row24_traceSegment_031_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 432 9 9, g32p_row24_traceSegment_031_0432_0009, g32p_row24_traceSegment_031_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 450 9 9, g32p_row24_traceSegment_031_0450_0009, g32p_row24_traceSegment_031_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 432 18 18, g32p_row24_traceSegment_031_0432_0018, g32p_row24_traceSegment_031_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 468 9 9, g32p_row24_traceSegment_031_0468_0009, g32p_row24_traceSegment_031_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 486 9 9, g32p_row24_traceSegment_031_0486_0009, g32p_row24_traceSegment_031_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 468 18 18, g32p_row24_traceSegment_031_0468_0018, g32p_row24_traceSegment_031_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 432 36 36, g32p_row24_traceSegment_031_0432_0036, g32p_row24_traceSegment_031_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 504 9 9, g32p_row24_traceSegment_031_0504_0009, g32p_row24_traceSegment_031_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 522 9 9, g32p_row24_traceSegment_031_0522_0009, g32p_row24_traceSegment_031_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 504 18 18, g32p_row24_traceSegment_031_0504_0018, g32p_row24_traceSegment_031_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 540 9 9, g32p_row24_traceSegment_031_0540_0009, g32p_row24_traceSegment_031_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 558 9 9, g32p_row24_traceSegment_031_0558_0009, g32p_row24_traceSegment_031_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 540 18 18, g32p_row24_traceSegment_031_0540_0018, g32p_row24_traceSegment_031_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 504 36 36, g32p_row24_traceSegment_031_0504_0036, g32p_row24_traceSegment_031_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 432 72 72, g32p_row24_traceSegment_031_0432_0072, g32p_row24_traceSegment_031_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_031 288 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 288 144 144, g32p_row24_traceSegment_031_0288_0144, g32p_row24_traceSegment_031_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_031 0 576 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 288 288, g32p_row24_traceSegment_031_0000_0288, g32p_row24_traceSegment_031_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 576 9 9, g32p_row24_traceSegment_031_0576_0009, g32p_row24_traceSegment_031_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 594 9 9, g32p_row24_traceSegment_031_0594_0009, g32p_row24_traceSegment_031_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 576 18 18, g32p_row24_traceSegment_031_0576_0018, g32p_row24_traceSegment_031_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 612 9 9, g32p_row24_traceSegment_031_0612_0009, g32p_row24_traceSegment_031_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 630 9 9, g32p_row24_traceSegment_031_0630_0009, g32p_row24_traceSegment_031_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 612 18 18, g32p_row24_traceSegment_031_0612_0018, g32p_row24_traceSegment_031_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 576 36 36, g32p_row24_traceSegment_031_0576_0036, g32p_row24_traceSegment_031_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 648 9 9, g32p_row24_traceSegment_031_0648_0009, g32p_row24_traceSegment_031_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 675 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 666 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 666 9 9, g32p_row24_traceSegment_031_0666_0009, g32p_row24_traceSegment_031_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 648 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 648 18 18, g32p_row24_traceSegment_031_0648_0018, g32p_row24_traceSegment_031_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 684 9 9, g32p_row24_traceSegment_031_0684_0009, g32p_row24_traceSegment_031_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 702 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 702 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 702 9 9, g32p_row24_traceSegment_031_0702_0009, g32p_row24_traceSegment_031_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 684 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 684 18 18, g32p_row24_traceSegment_031_0684_0018, g32p_row24_traceSegment_031_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 648 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 648 36 36, g32p_row24_traceSegment_031_0648_0036, g32p_row24_traceSegment_031_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 576 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 576 72 72, g32p_row24_traceSegment_031_0576_0072, g32p_row24_traceSegment_031_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 720 9 9, g32p_row24_traceSegment_031_0720_0009, g32p_row24_traceSegment_031_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 738 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 738 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 738 9 9, g32p_row24_traceSegment_031_0738_0009, g32p_row24_traceSegment_031_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 720 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 720 18 18, g32p_row24_traceSegment_031_0720_0018, g32p_row24_traceSegment_031_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 756 9 9, g32p_row24_traceSegment_031_0756_0009, g32p_row24_traceSegment_031_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 774 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 774 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 774 9 9, g32p_row24_traceSegment_031_0774_0009, g32p_row24_traceSegment_031_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 756 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 756 18 18, g32p_row24_traceSegment_031_0756_0018, g32p_row24_traceSegment_031_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 720 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 720 36 36, g32p_row24_traceSegment_031_0720_0036, g32p_row24_traceSegment_031_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 792 9 9, g32p_row24_traceSegment_031_0792_0009, g32p_row24_traceSegment_031_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 810 9 9, g32p_row24_traceSegment_031_0810_0009, g32p_row24_traceSegment_031_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 792 18 18, g32p_row24_traceSegment_031_0792_0018, g32p_row24_traceSegment_031_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 828 9 9, g32p_row24_traceSegment_031_0828_0009, g32p_row24_traceSegment_031_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 846 9 9, g32p_row24_traceSegment_031_0846_0009, g32p_row24_traceSegment_031_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 828 18 18, g32p_row24_traceSegment_031_0828_0018, g32p_row24_traceSegment_031_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 792 36 36, g32p_row24_traceSegment_031_0792_0036, g32p_row24_traceSegment_031_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 720 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 720 72 72, g32p_row24_traceSegment_031_0720_0072, g32p_row24_traceSegment_031_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_031 576 288 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 576 144 144, g32p_row24_traceSegment_031_0576_0144, g32p_row24_traceSegment_031_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 864 9 9, g32p_row24_traceSegment_031_0864_0009, g32p_row24_traceSegment_031_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 882 9 9, g32p_row24_traceSegment_031_0882_0009, g32p_row24_traceSegment_031_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 864 18 18, g32p_row24_traceSegment_031_0864_0018, g32p_row24_traceSegment_031_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 900 9 9, g32p_row24_traceSegment_031_0900_0009, g32p_row24_traceSegment_031_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 918 9 9, g32p_row24_traceSegment_031_0918_0009, g32p_row24_traceSegment_031_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 900 18 18, g32p_row24_traceSegment_031_0900_0018, g32p_row24_traceSegment_031_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 864 36 36, g32p_row24_traceSegment_031_0864_0036, g32p_row24_traceSegment_031_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 936 9 9, g32p_row24_traceSegment_031_0936_0009, g32p_row24_traceSegment_031_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 954 9 9, g32p_row24_traceSegment_031_0954_0009, g32p_row24_traceSegment_031_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 936 18 18, g32p_row24_traceSegment_031_0936_0018, g32p_row24_traceSegment_031_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 972 9 9, g32p_row24_traceSegment_031_0972_0009, g32p_row24_traceSegment_031_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 990 9 9, g32p_row24_traceSegment_031_0990_0009, g32p_row24_traceSegment_031_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 972 18 18, g32p_row24_traceSegment_031_0972_0018, g32p_row24_traceSegment_031_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 936 36 36, g32p_row24_traceSegment_031_0936_0036, g32p_row24_traceSegment_031_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 864 72 72, g32p_row24_traceSegment_031_0864_0072, g32p_row24_traceSegment_031_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1008 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1017 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1008 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1008 9 9, g32p_row24_traceSegment_031_1008_0009, g32p_row24_traceSegment_031_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1026 9 9, g32p_row24_traceSegment_031_1026_0009, g32p_row24_traceSegment_031_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 1008 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1008 18 18, g32p_row24_traceSegment_031_1008_0018, g32p_row24_traceSegment_031_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1044 9 9, g32p_row24_traceSegment_031_1044_0009, g32p_row24_traceSegment_031_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1062 9 9, g32p_row24_traceSegment_031_1062_0009, g32p_row24_traceSegment_031_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1044 18 18, g32p_row24_traceSegment_031_1044_0018, g32p_row24_traceSegment_031_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 1008 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1008 36 36, g32p_row24_traceSegment_031_1008_0036, g32p_row24_traceSegment_031_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1080 9 9, g32p_row24_traceSegment_031_1080_0009, g32p_row24_traceSegment_031_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1098 9 9, g32p_row24_traceSegment_031_1098_0009, g32p_row24_traceSegment_031_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1080 18 18, g32p_row24_traceSegment_031_1080_0018, g32p_row24_traceSegment_031_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1116 9 9, g32p_row24_traceSegment_031_1116_0009, g32p_row24_traceSegment_031_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_031 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_031_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_031 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1134 9 9, g32p_row24_traceSegment_031_1134_0009, g32p_row24_traceSegment_031_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_031 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1116 18 18, g32p_row24_traceSegment_031_1116_0018, g32p_row24_traceSegment_031_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_031 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1080 36 36, g32p_row24_traceSegment_031_1080_0036, g32p_row24_traceSegment_031_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_031_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_031 1008 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 1008 72 72, g32p_row24_traceSegment_031_1008_0072, g32p_row24_traceSegment_031_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_031 864 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 864 144 144, g32p_row24_traceSegment_031_0864_0144, g32p_row24_traceSegment_031_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_031 576 576 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 576 288 288, g32p_row24_traceSegment_031_0576_0288, g32p_row24_traceSegment_031_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_031_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_031 0 1152 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_031 0 576 576, g32p_row24_traceSegment_031_0000_0576, g32p_row24_traceSegment_031_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 31 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_031_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row24_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 0) (g32p_literalTraceValue 23 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_000]
  decide +kernel

theorem g32p_row24_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 5) (g32p_literalTraceValue 23 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_005]
  decide +kernel

theorem g32p_row24_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 6) (g32p_literalTraceValue 23 6)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_006]
  decide +kernel

theorem g32p_row24_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 10) (g32p_literalTraceValue 23 10)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_010]
  decide +kernel

theorem g32p_row24_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 13) (g32p_literalTraceValue 23 13)
      [1, -1, 1] [0, 0, 6912, 6912] = true := by
  rw [g32p_row24_traceCoefficients_013]
  decide +kernel

theorem g32p_row24_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 15) (g32p_literalTraceValue 23 15)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_015]
  decide +kernel

theorem g32p_row24_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 18) (g32p_literalTraceValue 23 18)
      [1, -1, 1] [41472, 41472] = true := by
  rw [g32p_row24_traceCoefficients_018]
  decide +kernel

theorem g32p_row24_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 31) (g32p_literalTraceValue 23 31)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_031]
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

private def g32p_row24_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_032_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 9 9, g32p_row24_traceSegment_032_0000_0009, g32p_row24_traceSegment_032_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 27 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 18 9 9, g32p_row24_traceSegment_032_0018_0009, g32p_row24_traceSegment_032_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 0 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 18 18, g32p_row24_traceSegment_032_0000_0018, g32p_row24_traceSegment_032_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 45 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 36 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 36 9 9, g32p_row24_traceSegment_032_0036_0009, g32p_row24_traceSegment_032_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 54 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 54 9 9, g32p_row24_traceSegment_032_0054_0009, g32p_row24_traceSegment_032_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 36 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 36 18 18, g32p_row24_traceSegment_032_0036_0018, g32p_row24_traceSegment_032_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 0 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 36 36, g32p_row24_traceSegment_032_0000_0036, g32p_row24_traceSegment_032_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 81 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 72 9 9, g32p_row24_traceSegment_032_0072_0009, g32p_row24_traceSegment_032_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 90 9 9, g32p_row24_traceSegment_032_0090_0009, g32p_row24_traceSegment_032_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 72 18 18, g32p_row24_traceSegment_032_0072_0018, g32p_row24_traceSegment_032_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 108 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 117 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 108 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 108 9 9, g32p_row24_traceSegment_032_0108_0009, g32p_row24_traceSegment_032_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 126 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 126 9 9, g32p_row24_traceSegment_032_0126_0009, g32p_row24_traceSegment_032_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 108 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 108 18 18, g32p_row24_traceSegment_032_0108_0018, g32p_row24_traceSegment_032_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 72 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 72 36 36, g32p_row24_traceSegment_032_0072_0036, g32p_row24_traceSegment_032_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 0 144 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 72 72, g32p_row24_traceSegment_032_0000_0072, g32p_row24_traceSegment_032_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 144 9 9, g32p_row24_traceSegment_032_0144_0009, g32p_row24_traceSegment_032_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 162 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 162 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 162 9 9, g32p_row24_traceSegment_032_0162_0009, g32p_row24_traceSegment_032_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 144 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 144 18 18, g32p_row24_traceSegment_032_0144_0018, g32p_row24_traceSegment_032_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 180 9 9, g32p_row24_traceSegment_032_0180_0009, g32p_row24_traceSegment_032_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 198 9 9, g32p_row24_traceSegment_032_0198_0009, g32p_row24_traceSegment_032_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 180 18 18, g32p_row24_traceSegment_032_0180_0018, g32p_row24_traceSegment_032_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 144 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 144 36 36, g32p_row24_traceSegment_032_0144_0036, g32p_row24_traceSegment_032_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 216 9 9, g32p_row24_traceSegment_032_0216_0009, g32p_row24_traceSegment_032_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 243 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 234 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 234 9 9, g32p_row24_traceSegment_032_0234_0009, g32p_row24_traceSegment_032_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 216 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 216 18 18, g32p_row24_traceSegment_032_0216_0018, g32p_row24_traceSegment_032_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 252 9 9, g32p_row24_traceSegment_032_0252_0009, g32p_row24_traceSegment_032_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 270 9 9, g32p_row24_traceSegment_032_0270_0009, g32p_row24_traceSegment_032_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 252 18 18, g32p_row24_traceSegment_032_0252_0018, g32p_row24_traceSegment_032_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 216 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 216 36 36, g32p_row24_traceSegment_032_0216_0036, g32p_row24_traceSegment_032_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 144 72 72, g32p_row24_traceSegment_032_0144_0072, g32p_row24_traceSegment_032_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_032 0 288 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 144 144, g32p_row24_traceSegment_032_0000_0144, g32p_row24_traceSegment_032_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 288 9 9, g32p_row24_traceSegment_032_0288_0009, g32p_row24_traceSegment_032_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 306 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 306 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 306 9 9, g32p_row24_traceSegment_032_0306_0009, g32p_row24_traceSegment_032_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 288 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 288 18 18, g32p_row24_traceSegment_032_0288_0018, g32p_row24_traceSegment_032_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 333 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 324 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 324 9 9, g32p_row24_traceSegment_032_0324_0009, g32p_row24_traceSegment_032_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 342 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 342 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 342 9 9, g32p_row24_traceSegment_032_0342_0009, g32p_row24_traceSegment_032_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 324 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 324 18 18, g32p_row24_traceSegment_032_0324_0018, g32p_row24_traceSegment_032_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 288 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 288 36 36, g32p_row24_traceSegment_032_0288_0036, g32p_row24_traceSegment_032_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 360 9 9, g32p_row24_traceSegment_032_0360_0009, g32p_row24_traceSegment_032_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 378 9 9, g32p_row24_traceSegment_032_0378_0009, g32p_row24_traceSegment_032_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 360 18 18, g32p_row24_traceSegment_032_0360_0018, g32p_row24_traceSegment_032_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 396 9 9, g32p_row24_traceSegment_032_0396_0009, g32p_row24_traceSegment_032_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 414 9 9, g32p_row24_traceSegment_032_0414_0009, g32p_row24_traceSegment_032_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 396 18 18, g32p_row24_traceSegment_032_0396_0018, g32p_row24_traceSegment_032_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 360 36 36, g32p_row24_traceSegment_032_0360_0036, g32p_row24_traceSegment_032_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 288 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 288 72 72, g32p_row24_traceSegment_032_0288_0072, g32p_row24_traceSegment_032_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 432 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 441 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 432 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 432 9 9, g32p_row24_traceSegment_032_0432_0009, g32p_row24_traceSegment_032_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 459 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 450 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 450 9 9, g32p_row24_traceSegment_032_0450_0009, g32p_row24_traceSegment_032_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 432 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 432 18 18, g32p_row24_traceSegment_032_0432_0018, g32p_row24_traceSegment_032_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 468 9 9, g32p_row24_traceSegment_032_0468_0009, g32p_row24_traceSegment_032_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 486 9 9, g32p_row24_traceSegment_032_0486_0009, g32p_row24_traceSegment_032_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 468 18 18, g32p_row24_traceSegment_032_0468_0018, g32p_row24_traceSegment_032_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 432 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 432 36 36, g32p_row24_traceSegment_032_0432_0036, g32p_row24_traceSegment_032_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 504 9 9, g32p_row24_traceSegment_032_0504_0009, g32p_row24_traceSegment_032_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 522 9 9, g32p_row24_traceSegment_032_0522_0009, g32p_row24_traceSegment_032_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 504 18 18, g32p_row24_traceSegment_032_0504_0018, g32p_row24_traceSegment_032_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 540 9 9, g32p_row24_traceSegment_032_0540_0009, g32p_row24_traceSegment_032_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 558 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 558 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 558 9 9, g32p_row24_traceSegment_032_0558_0009, g32p_row24_traceSegment_032_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 540 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 540 18 18, g32p_row24_traceSegment_032_0540_0018, g32p_row24_traceSegment_032_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 504 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 504 36 36, g32p_row24_traceSegment_032_0504_0036, g32p_row24_traceSegment_032_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 432 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 432 72 72, g32p_row24_traceSegment_032_0432_0072, g32p_row24_traceSegment_032_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_032 288 288 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 288 144 144, g32p_row24_traceSegment_032_0288_0144, g32p_row24_traceSegment_032_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_032 0 576 = [0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 288 288, g32p_row24_traceSegment_032_0000_0288, g32p_row24_traceSegment_032_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 576 9 9, g32p_row24_traceSegment_032_0576_0009, g32p_row24_traceSegment_032_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 594 9 9, g32p_row24_traceSegment_032_0594_0009, g32p_row24_traceSegment_032_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 576 18 18, g32p_row24_traceSegment_032_0576_0018, g32p_row24_traceSegment_032_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 612 9 9, g32p_row24_traceSegment_032_0612_0009, g32p_row24_traceSegment_032_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 630 9 9, g32p_row24_traceSegment_032_0630_0009, g32p_row24_traceSegment_032_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 612 18 18, g32p_row24_traceSegment_032_0612_0018, g32p_row24_traceSegment_032_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 576 36 36, g32p_row24_traceSegment_032_0576_0036, g32p_row24_traceSegment_032_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 648 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 657 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 648 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 648 9 9, g32p_row24_traceSegment_032_0648_0009, g32p_row24_traceSegment_032_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 666 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 666 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 666 9 9, g32p_row24_traceSegment_032_0666_0009, g32p_row24_traceSegment_032_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 648 36 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 648 18 18, g32p_row24_traceSegment_032_0648_0018, g32p_row24_traceSegment_032_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 693 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 684 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 684 9 9, g32p_row24_traceSegment_032_0684_0009, g32p_row24_traceSegment_032_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 702 9 9, g32p_row24_traceSegment_032_0702_0009, g32p_row24_traceSegment_032_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 684 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 684 18 18, g32p_row24_traceSegment_032_0684_0018, g32p_row24_traceSegment_032_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 648 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 648 36 36, g32p_row24_traceSegment_032_0648_0036, g32p_row24_traceSegment_032_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 576 144 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 576 72 72, g32p_row24_traceSegment_032_0576_0072, g32p_row24_traceSegment_032_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 720 9 9, g32p_row24_traceSegment_032_0720_0009, g32p_row24_traceSegment_032_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 738 9 9, g32p_row24_traceSegment_032_0738_0009, g32p_row24_traceSegment_032_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 720 18 18, g32p_row24_traceSegment_032_0720_0018, g32p_row24_traceSegment_032_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 756 9 9, g32p_row24_traceSegment_032_0756_0009, g32p_row24_traceSegment_032_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 774 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 783 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 774 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 774 9 9, g32p_row24_traceSegment_032_0774_0009, g32p_row24_traceSegment_032_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 756 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 756 18 18, g32p_row24_traceSegment_032_0756_0018, g32p_row24_traceSegment_032_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 720 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 720 36 36, g32p_row24_traceSegment_032_0720_0036, g32p_row24_traceSegment_032_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 792 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 792 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 792 9 9, g32p_row24_traceSegment_032_0792_0009, g32p_row24_traceSegment_032_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 810 9 9, g32p_row24_traceSegment_032_0810_0009, g32p_row24_traceSegment_032_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 792 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 792 18 18, g32p_row24_traceSegment_032_0792_0018, g32p_row24_traceSegment_032_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 828 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 828 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 828 9 9, g32p_row24_traceSegment_032_0828_0009, g32p_row24_traceSegment_032_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 846 9 9, g32p_row24_traceSegment_032_0846_0009, g32p_row24_traceSegment_032_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 828 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 828 18 18, g32p_row24_traceSegment_032_0828_0018, g32p_row24_traceSegment_032_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 792 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 792 36 36, g32p_row24_traceSegment_032_0792_0036, g32p_row24_traceSegment_032_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 720 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 720 72 72, g32p_row24_traceSegment_032_0720_0072, g32p_row24_traceSegment_032_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_032 576 288 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 576 144 144, g32p_row24_traceSegment_032_0576_0144, g32p_row24_traceSegment_032_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 864 9 9, g32p_row24_traceSegment_032_0864_0009, g32p_row24_traceSegment_032_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 882 9 9, g32p_row24_traceSegment_032_0882_0009, g32p_row24_traceSegment_032_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 864 18 18, g32p_row24_traceSegment_032_0864_0018, g32p_row24_traceSegment_032_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 900 9 9, g32p_row24_traceSegment_032_0900_0009, g32p_row24_traceSegment_032_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 918 9 9, g32p_row24_traceSegment_032_0918_0009, g32p_row24_traceSegment_032_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 900 18 18, g32p_row24_traceSegment_032_0900_0018, g32p_row24_traceSegment_032_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 864 36 36, g32p_row24_traceSegment_032_0864_0036, g32p_row24_traceSegment_032_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 936 9 9, g32p_row24_traceSegment_032_0936_0009, g32p_row24_traceSegment_032_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 954 9 9, g32p_row24_traceSegment_032_0954_0009, g32p_row24_traceSegment_032_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 936 18 18, g32p_row24_traceSegment_032_0936_0018, g32p_row24_traceSegment_032_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 972 9 9, g32p_row24_traceSegment_032_0972_0009, g32p_row24_traceSegment_032_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 990 9 9, g32p_row24_traceSegment_032_0990_0009, g32p_row24_traceSegment_032_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 972 18 18, g32p_row24_traceSegment_032_0972_0018, g32p_row24_traceSegment_032_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 936 36 36, g32p_row24_traceSegment_032_0936_0036, g32p_row24_traceSegment_032_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 864 72 72, g32p_row24_traceSegment_032_0864_0072, g32p_row24_traceSegment_032_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1008 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1008 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1008 9 9, g32p_row24_traceSegment_032_1008_0009, g32p_row24_traceSegment_032_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1026 9 9, g32p_row24_traceSegment_032_1026_0009, g32p_row24_traceSegment_032_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 1008 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1008 18 18, g32p_row24_traceSegment_032_1008_0018, g32p_row24_traceSegment_032_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1044 9 9, g32p_row24_traceSegment_032_1044_0009, g32p_row24_traceSegment_032_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1071 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1062 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1062 9 9, g32p_row24_traceSegment_032_1062_0009, g32p_row24_traceSegment_032_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 1044 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1044 18 18, g32p_row24_traceSegment_032_1044_0018, g32p_row24_traceSegment_032_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 1008 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1008 36 36, g32p_row24_traceSegment_032_1008_0036, g32p_row24_traceSegment_032_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1080 9 9, g32p_row24_traceSegment_032_1080_0009, g32p_row24_traceSegment_032_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1098 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1098 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1098 9 9, g32p_row24_traceSegment_032_1098_0009, g32p_row24_traceSegment_032_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 1080 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1080 18 18, g32p_row24_traceSegment_032_1080_0018, g32p_row24_traceSegment_032_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1116 9 9, g32p_row24_traceSegment_032_1116_0009, g32p_row24_traceSegment_032_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_032 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_032_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_032 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1134 9 9, g32p_row24_traceSegment_032_1134_0009, g32p_row24_traceSegment_032_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_032 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1116 18 18, g32p_row24_traceSegment_032_1116_0018, g32p_row24_traceSegment_032_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_032 1080 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1080 36 36, g32p_row24_traceSegment_032_1080_0036, g32p_row24_traceSegment_032_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_032_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_032 1008 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 1008 72 72, g32p_row24_traceSegment_032_1008_0072, g32p_row24_traceSegment_032_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_032 864 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 864 144 144, g32p_row24_traceSegment_032_0864_0144, g32p_row24_traceSegment_032_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_032 576 576 = [0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 576 288 288, g32p_row24_traceSegment_032_0576_0288, g32p_row24_traceSegment_032_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_032_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_032 0 1152 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_032 0 576 576, g32p_row24_traceSegment_032_0000_0576, g32p_row24_traceSegment_032_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 32 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_032_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_034_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 0 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 9 9, g32p_row24_traceSegment_034_0000_0009, g32p_row24_traceSegment_034_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 27 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 18 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 18 9 9, g32p_row24_traceSegment_034_0018_0009, g32p_row24_traceSegment_034_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 0 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 18 18, g32p_row24_traceSegment_034_0000_0018, g32p_row24_traceSegment_034_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 36 9 9, g32p_row24_traceSegment_034_0036_0009, g32p_row24_traceSegment_034_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 54 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 54 9 9, g32p_row24_traceSegment_034_0054_0009, g32p_row24_traceSegment_034_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 36 18 18, g32p_row24_traceSegment_034_0036_0018, g32p_row24_traceSegment_034_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 0 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 36 36, g32p_row24_traceSegment_034_0000_0036, g32p_row24_traceSegment_034_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 72 9 9, g32p_row24_traceSegment_034_0072_0009, g32p_row24_traceSegment_034_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 90 9 9, g32p_row24_traceSegment_034_0090_0009, g32p_row24_traceSegment_034_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 72 18 18, g32p_row24_traceSegment_034_0072_0018, g32p_row24_traceSegment_034_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 108 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 108 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 108 9 9, g32p_row24_traceSegment_034_0108_0009, g32p_row24_traceSegment_034_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 126 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 135 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 126 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 126 9 9, g32p_row24_traceSegment_034_0126_0009, g32p_row24_traceSegment_034_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 108 36 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 108 18 18, g32p_row24_traceSegment_034_0108_0018, g32p_row24_traceSegment_034_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 72 72 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 72 36 36, g32p_row24_traceSegment_034_0072_0036, g32p_row24_traceSegment_034_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 0 144 = [0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 72 72, g32p_row24_traceSegment_034_0000_0072, g32p_row24_traceSegment_034_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 144 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 153 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 144 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 144 9 9, g32p_row24_traceSegment_034_0144_0009, g32p_row24_traceSegment_034_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 171 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 162 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 162 9 9, g32p_row24_traceSegment_034_0162_0009, g32p_row24_traceSegment_034_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 144 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 144 18 18, g32p_row24_traceSegment_034_0144_0018, g32p_row24_traceSegment_034_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 180 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 189 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 180 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 180 9 9, g32p_row24_traceSegment_034_0180_0009, g32p_row24_traceSegment_034_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 198 9 9, g32p_row24_traceSegment_034_0198_0009, g32p_row24_traceSegment_034_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 180 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 180 18 18, g32p_row24_traceSegment_034_0180_0018, g32p_row24_traceSegment_034_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 144 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 144 36 36, g32p_row24_traceSegment_034_0144_0036, g32p_row24_traceSegment_034_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 216 9 9, g32p_row24_traceSegment_034_0216_0009, g32p_row24_traceSegment_034_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 234 9 9, g32p_row24_traceSegment_034_0234_0009, g32p_row24_traceSegment_034_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 216 18 18, g32p_row24_traceSegment_034_0216_0018, g32p_row24_traceSegment_034_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 252 9 9, g32p_row24_traceSegment_034_0252_0009, g32p_row24_traceSegment_034_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 279 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 270 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 270 9 9, g32p_row24_traceSegment_034_0270_0009, g32p_row24_traceSegment_034_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 252 18 18, g32p_row24_traceSegment_034_0252_0018, g32p_row24_traceSegment_034_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 216 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 216 36 36, g32p_row24_traceSegment_034_0216_0036, g32p_row24_traceSegment_034_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 144 144 = [0, 1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 144 72 72, g32p_row24_traceSegment_034_0144_0072, g32p_row24_traceSegment_034_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_034 0 288 = [0, 3, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 144 144, g32p_row24_traceSegment_034_0000_0144, g32p_row24_traceSegment_034_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 288 9 9, g32p_row24_traceSegment_034_0288_0009, g32p_row24_traceSegment_034_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 306 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 315 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 306 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 306 9 9, g32p_row24_traceSegment_034_0306_0009, g32p_row24_traceSegment_034_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 288 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 288 18 18, g32p_row24_traceSegment_034_0288_0018, g32p_row24_traceSegment_034_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 324 9 9, g32p_row24_traceSegment_034_0324_0009, g32p_row24_traceSegment_034_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 342 9 9, g32p_row24_traceSegment_034_0342_0009, g32p_row24_traceSegment_034_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 324 18 18, g32p_row24_traceSegment_034_0324_0018, g32p_row24_traceSegment_034_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 288 72 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 288 36 36, g32p_row24_traceSegment_034_0288_0036, g32p_row24_traceSegment_034_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 360 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 360 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 360 9 9, g32p_row24_traceSegment_034_0360_0009, g32p_row24_traceSegment_034_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 378 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 387 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 378 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 378 9 9, g32p_row24_traceSegment_034_0378_0009, g32p_row24_traceSegment_034_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 360 36 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 360 18 18, g32p_row24_traceSegment_034_0360_0018, g32p_row24_traceSegment_034_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 405 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 396 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 396 9 9, g32p_row24_traceSegment_034_0396_0009, g32p_row24_traceSegment_034_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 414 9 9, g32p_row24_traceSegment_034_0414_0009, g32p_row24_traceSegment_034_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 396 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 396 18 18, g32p_row24_traceSegment_034_0396_0018, g32p_row24_traceSegment_034_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 360 72 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 360 36 36, g32p_row24_traceSegment_034_0360_0036, g32p_row24_traceSegment_034_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 288 144 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 288 72 72, g32p_row24_traceSegment_034_0288_0072, g32p_row24_traceSegment_034_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 432 9 9, g32p_row24_traceSegment_034_0432_0009, g32p_row24_traceSegment_034_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 450 9 9, g32p_row24_traceSegment_034_0450_0009, g32p_row24_traceSegment_034_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 432 18 18, g32p_row24_traceSegment_034_0432_0018, g32p_row24_traceSegment_034_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 468 9 9, g32p_row24_traceSegment_034_0468_0009, g32p_row24_traceSegment_034_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 486 9 9, g32p_row24_traceSegment_034_0486_0009, g32p_row24_traceSegment_034_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 468 18 18, g32p_row24_traceSegment_034_0468_0018, g32p_row24_traceSegment_034_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 432 36 36, g32p_row24_traceSegment_034_0432_0036, g32p_row24_traceSegment_034_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 504 9 9, g32p_row24_traceSegment_034_0504_0009, g32p_row24_traceSegment_034_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 522 9 9, g32p_row24_traceSegment_034_0522_0009, g32p_row24_traceSegment_034_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 504 18 18, g32p_row24_traceSegment_034_0504_0018, g32p_row24_traceSegment_034_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 540 9 9, g32p_row24_traceSegment_034_0540_0009, g32p_row24_traceSegment_034_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 558 9 9, g32p_row24_traceSegment_034_0558_0009, g32p_row24_traceSegment_034_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 540 18 18, g32p_row24_traceSegment_034_0540_0018, g32p_row24_traceSegment_034_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 504 36 36, g32p_row24_traceSegment_034_0504_0036, g32p_row24_traceSegment_034_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 432 72 72, g32p_row24_traceSegment_034_0432_0072, g32p_row24_traceSegment_034_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_034 288 288 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 288 144 144, g32p_row24_traceSegment_034_0288_0144, g32p_row24_traceSegment_034_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_034 0 576 = [0, 7, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 288 288, g32p_row24_traceSegment_034_0000_0288, g32p_row24_traceSegment_034_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 576 9 9, g32p_row24_traceSegment_034_0576_0009, g32p_row24_traceSegment_034_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 594 9 9, g32p_row24_traceSegment_034_0594_0009, g32p_row24_traceSegment_034_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 576 18 18, g32p_row24_traceSegment_034_0576_0018, g32p_row24_traceSegment_034_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 612 9 9, g32p_row24_traceSegment_034_0612_0009, g32p_row24_traceSegment_034_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 630 9 9, g32p_row24_traceSegment_034_0630_0009, g32p_row24_traceSegment_034_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 612 18 18, g32p_row24_traceSegment_034_0612_0018, g32p_row24_traceSegment_034_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 576 36 36, g32p_row24_traceSegment_034_0576_0036, g32p_row24_traceSegment_034_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 648 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 657 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 648 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 648 9 9, g32p_row24_traceSegment_034_0648_0009, g32p_row24_traceSegment_034_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 666 9 9, g32p_row24_traceSegment_034_0666_0009, g32p_row24_traceSegment_034_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 648 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 648 18 18, g32p_row24_traceSegment_034_0648_0018, g32p_row24_traceSegment_034_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 693 9 = [0, 1, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 684 18 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 684 9 9, g32p_row24_traceSegment_034_0684_0009, g32p_row24_traceSegment_034_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 702 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 702 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 702 9 9, g32p_row24_traceSegment_034_0702_0009, g32p_row24_traceSegment_034_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 684 36 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 684 18 18, g32p_row24_traceSegment_034_0684_0018, g32p_row24_traceSegment_034_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 648 72 = [0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 648 36 36, g32p_row24_traceSegment_034_0648_0036, g32p_row24_traceSegment_034_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 576 144 = [0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 576 72 72, g32p_row24_traceSegment_034_0576_0072, g32p_row24_traceSegment_034_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 720 9 9, g32p_row24_traceSegment_034_0720_0009, g32p_row24_traceSegment_034_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 747 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 738 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 738 9 9, g32p_row24_traceSegment_034_0738_0009, g32p_row24_traceSegment_034_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 720 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 720 18 18, g32p_row24_traceSegment_034_0720_0018, g32p_row24_traceSegment_034_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 756 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 765 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 756 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 756 9 9, g32p_row24_traceSegment_034_0756_0009, g32p_row24_traceSegment_034_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 783 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 774 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 774 9 9, g32p_row24_traceSegment_034_0774_0009, g32p_row24_traceSegment_034_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 756 36 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 756 18 18, g32p_row24_traceSegment_034_0756_0018, g32p_row24_traceSegment_034_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 720 72 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 720 36 36, g32p_row24_traceSegment_034_0720_0036, g32p_row24_traceSegment_034_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 801 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 792 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 792 9 9, g32p_row24_traceSegment_034_0792_0009, g32p_row24_traceSegment_034_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 810 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 819 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 810 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 810 9 9, g32p_row24_traceSegment_034_0810_0009, g32p_row24_traceSegment_034_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 792 36 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 792 18 18, g32p_row24_traceSegment_034_0792_0018, g32p_row24_traceSegment_034_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 828 9 9, g32p_row24_traceSegment_034_0828_0009, g32p_row24_traceSegment_034_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 846 9 9, g32p_row24_traceSegment_034_0846_0009, g32p_row24_traceSegment_034_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 828 18 18, g32p_row24_traceSegment_034_0828_0018, g32p_row24_traceSegment_034_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 792 72 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 792 36 36, g32p_row24_traceSegment_034_0792_0036, g32p_row24_traceSegment_034_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 720 144 = [0, 5, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 720 72 72, g32p_row24_traceSegment_034_0720_0072, g32p_row24_traceSegment_034_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_034 576 288 = [0, 7, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 576 144 144, g32p_row24_traceSegment_034_0576_0144, g32p_row24_traceSegment_034_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 864 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 864 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 864 9 9, g32p_row24_traceSegment_034_0864_0009, g32p_row24_traceSegment_034_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 882 9 9, g32p_row24_traceSegment_034_0882_0009, g32p_row24_traceSegment_034_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 864 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 864 18 18, g32p_row24_traceSegment_034_0864_0018, g32p_row24_traceSegment_034_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 900 9 = [0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 900 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 900 9 9, g32p_row24_traceSegment_034_0900_0009, g32p_row24_traceSegment_034_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 918 9 9, g32p_row24_traceSegment_034_0918_0009, g32p_row24_traceSegment_034_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 900 36 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 900 18 18, g32p_row24_traceSegment_034_0900_0018, g32p_row24_traceSegment_034_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 864 72 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 864 36 36, g32p_row24_traceSegment_034_0864_0036, g32p_row24_traceSegment_034_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 936 9 9, g32p_row24_traceSegment_034_0936_0009, g32p_row24_traceSegment_034_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 954 9 9, g32p_row24_traceSegment_034_0954_0009, g32p_row24_traceSegment_034_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 936 18 18, g32p_row24_traceSegment_034_0936_0018, g32p_row24_traceSegment_034_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 972 9 9, g32p_row24_traceSegment_034_0972_0009, g32p_row24_traceSegment_034_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 990 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 990 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 990 9 9, g32p_row24_traceSegment_034_0990_0009, g32p_row24_traceSegment_034_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 972 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 972 18 18, g32p_row24_traceSegment_034_0972_0018, g32p_row24_traceSegment_034_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 936 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 936 36 36, g32p_row24_traceSegment_034_0936_0036, g32p_row24_traceSegment_034_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 864 144 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 864 72 72, g32p_row24_traceSegment_034_0864_0072, g32p_row24_traceSegment_034_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1008 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1017 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1008 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1008 9 9, g32p_row24_traceSegment_034_1008_0009, g32p_row24_traceSegment_034_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1026 9 9, g32p_row24_traceSegment_034_1026_0009, g32p_row24_traceSegment_034_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 1008 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1008 18 18, g32p_row24_traceSegment_034_1008_0018, g32p_row24_traceSegment_034_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1053 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1044 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1044 9 9, g32p_row24_traceSegment_034_1044_0009, g32p_row24_traceSegment_034_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1071 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1062 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1062 9 9, g32p_row24_traceSegment_034_1062_0009, g32p_row24_traceSegment_034_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 1044 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1044 18 18, g32p_row24_traceSegment_034_1044_0018, g32p_row24_traceSegment_034_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 1008 72 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1008 36 36, g32p_row24_traceSegment_034_1008_0036, g32p_row24_traceSegment_034_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1080 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1089 9 = [0, 3, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1080 18 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1080 9 9, g32p_row24_traceSegment_034_1080_0009, g32p_row24_traceSegment_034_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1098 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1098 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1098 9 9, g32p_row24_traceSegment_034_1098_0009, g32p_row24_traceSegment_034_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 1080 36 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1080 18 18, g32p_row24_traceSegment_034_1080_0018, g32p_row24_traceSegment_034_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1116 9 9, g32p_row24_traceSegment_034_1116_0009, g32p_row24_traceSegment_034_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_034 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_034_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_034 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1134 9 9, g32p_row24_traceSegment_034_1134_0009, g32p_row24_traceSegment_034_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_034 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1116 18 18, g32p_row24_traceSegment_034_1116_0018, g32p_row24_traceSegment_034_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_034 1080 72 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1080 36 36, g32p_row24_traceSegment_034_1080_0036, g32p_row24_traceSegment_034_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_034_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_034 1008 144 = [0, 7, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 1008 72 72, g32p_row24_traceSegment_034_1008_0072, g32p_row24_traceSegment_034_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_034 864 288 = [0, 10, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 864 144 144, g32p_row24_traceSegment_034_0864_0144, g32p_row24_traceSegment_034_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_034 576 576 = [0, 17, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 576 288 288, g32p_row24_traceSegment_034_0576_0288, g32p_row24_traceSegment_034_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_034_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_034 0 1152 = [0, 24, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_034 0 576 576, g32p_row24_traceSegment_034_0000_0576, g32p_row24_traceSegment_034_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 34 = [0, 24, 0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_034_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_035_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 9 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 0 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 9 9, g32p_row24_traceSegment_035_0000_0009, g32p_row24_traceSegment_035_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 27 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 18 9 9, g32p_row24_traceSegment_035_0018_0009, g32p_row24_traceSegment_035_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 0 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 18 18, g32p_row24_traceSegment_035_0000_0018, g32p_row24_traceSegment_035_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 36 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 45 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 36 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 36 9 9, g32p_row24_traceSegment_035_0036_0009, g32p_row24_traceSegment_035_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 54 9 9, g32p_row24_traceSegment_035_0054_0009, g32p_row24_traceSegment_035_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 36 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 36 18 18, g32p_row24_traceSegment_035_0036_0018, g32p_row24_traceSegment_035_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 0 72 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 36 36, g32p_row24_traceSegment_035_0000_0036, g32p_row24_traceSegment_035_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 81 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 72 9 9, g32p_row24_traceSegment_035_0072_0009, g32p_row24_traceSegment_035_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 90 9 9, g32p_row24_traceSegment_035_0090_0009, g32p_row24_traceSegment_035_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 72 18 18, g32p_row24_traceSegment_035_0072_0018, g32p_row24_traceSegment_035_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 108 9 9, g32p_row24_traceSegment_035_0108_0009, g32p_row24_traceSegment_035_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 135 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 126 9 9, g32p_row24_traceSegment_035_0126_0009, g32p_row24_traceSegment_035_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 108 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 108 18 18, g32p_row24_traceSegment_035_0108_0018, g32p_row24_traceSegment_035_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 72 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 72 36 36, g32p_row24_traceSegment_035_0072_0036, g32p_row24_traceSegment_035_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 0 144 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 72 72, g32p_row24_traceSegment_035_0000_0072, g32p_row24_traceSegment_035_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 144 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 153 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 144 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 144 9 9, g32p_row24_traceSegment_035_0144_0009, g32p_row24_traceSegment_035_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 171 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 162 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 162 9 9, g32p_row24_traceSegment_035_0162_0009, g32p_row24_traceSegment_035_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 144 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 144 18 18, g32p_row24_traceSegment_035_0144_0018, g32p_row24_traceSegment_035_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 180 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 180 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 180 9 9, g32p_row24_traceSegment_035_0180_0009, g32p_row24_traceSegment_035_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 198 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 198 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 198 9 9, g32p_row24_traceSegment_035_0198_0009, g32p_row24_traceSegment_035_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 180 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 180 18 18, g32p_row24_traceSegment_035_0180_0018, g32p_row24_traceSegment_035_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 144 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 144 36 36, g32p_row24_traceSegment_035_0144_0036, g32p_row24_traceSegment_035_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 216 9 9, g32p_row24_traceSegment_035_0216_0009, g32p_row24_traceSegment_035_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 234 9 9, g32p_row24_traceSegment_035_0234_0009, g32p_row24_traceSegment_035_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 216 18 18, g32p_row24_traceSegment_035_0216_0018, g32p_row24_traceSegment_035_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 252 9 9, g32p_row24_traceSegment_035_0252_0009, g32p_row24_traceSegment_035_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 270 9 9, g32p_row24_traceSegment_035_0270_0009, g32p_row24_traceSegment_035_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 252 18 18, g32p_row24_traceSegment_035_0252_0018, g32p_row24_traceSegment_035_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 216 36 36, g32p_row24_traceSegment_035_0216_0036, g32p_row24_traceSegment_035_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 144 144 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 144 72 72, g32p_row24_traceSegment_035_0144_0072, g32p_row24_traceSegment_035_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_035 0 288 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 144 144, g32p_row24_traceSegment_035_0000_0144, g32p_row24_traceSegment_035_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 288 9 9, g32p_row24_traceSegment_035_0288_0009, g32p_row24_traceSegment_035_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 315 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 306 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 306 9 9, g32p_row24_traceSegment_035_0306_0009, g32p_row24_traceSegment_035_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 288 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 288 18 18, g32p_row24_traceSegment_035_0288_0018, g32p_row24_traceSegment_035_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 333 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 324 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 324 9 9, g32p_row24_traceSegment_035_0324_0009, g32p_row24_traceSegment_035_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 342 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 342 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 342 9 9, g32p_row24_traceSegment_035_0342_0009, g32p_row24_traceSegment_035_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 324 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 324 18 18, g32p_row24_traceSegment_035_0324_0018, g32p_row24_traceSegment_035_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 288 72 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 288 36 36, g32p_row24_traceSegment_035_0288_0036, g32p_row24_traceSegment_035_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 360 9 9, g32p_row24_traceSegment_035_0360_0009, g32p_row24_traceSegment_035_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 378 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 378 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 378 9 9, g32p_row24_traceSegment_035_0378_0009, g32p_row24_traceSegment_035_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 360 18 18, g32p_row24_traceSegment_035_0360_0018, g32p_row24_traceSegment_035_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 405 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 396 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 396 9 9, g32p_row24_traceSegment_035_0396_0009, g32p_row24_traceSegment_035_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 414 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 414 9 9, g32p_row24_traceSegment_035_0414_0009, g32p_row24_traceSegment_035_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 396 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 396 18 18, g32p_row24_traceSegment_035_0396_0018, g32p_row24_traceSegment_035_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 360 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 360 36 36, g32p_row24_traceSegment_035_0360_0036, g32p_row24_traceSegment_035_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 288 144 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 288 72 72, g32p_row24_traceSegment_035_0288_0072, g32p_row24_traceSegment_035_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 441 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 432 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 432 9 9, g32p_row24_traceSegment_035_0432_0009, g32p_row24_traceSegment_035_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 450 9 9, g32p_row24_traceSegment_035_0450_0009, g32p_row24_traceSegment_035_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 432 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 432 18 18, g32p_row24_traceSegment_035_0432_0018, g32p_row24_traceSegment_035_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 468 9 9, g32p_row24_traceSegment_035_0468_0009, g32p_row24_traceSegment_035_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 486 9 9, g32p_row24_traceSegment_035_0486_0009, g32p_row24_traceSegment_035_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 468 18 18, g32p_row24_traceSegment_035_0468_0018, g32p_row24_traceSegment_035_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 432 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 432 36 36, g32p_row24_traceSegment_035_0432_0036, g32p_row24_traceSegment_035_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 504 9 9, g32p_row24_traceSegment_035_0504_0009, g32p_row24_traceSegment_035_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 522 9 9, g32p_row24_traceSegment_035_0522_0009, g32p_row24_traceSegment_035_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 504 18 18, g32p_row24_traceSegment_035_0504_0018, g32p_row24_traceSegment_035_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 540 9 9, g32p_row24_traceSegment_035_0540_0009, g32p_row24_traceSegment_035_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 558 9 9, g32p_row24_traceSegment_035_0558_0009, g32p_row24_traceSegment_035_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 540 18 18, g32p_row24_traceSegment_035_0540_0018, g32p_row24_traceSegment_035_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 504 36 36, g32p_row24_traceSegment_035_0504_0036, g32p_row24_traceSegment_035_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 432 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 432 72 72, g32p_row24_traceSegment_035_0432_0072, g32p_row24_traceSegment_035_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_035 288 288 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 288 144 144, g32p_row24_traceSegment_035_0288_0144, g32p_row24_traceSegment_035_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_035 0 576 = [0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 288 288, g32p_row24_traceSegment_035_0000_0288, g32p_row24_traceSegment_035_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 576 9 9, g32p_row24_traceSegment_035_0576_0009, g32p_row24_traceSegment_035_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 594 9 9, g32p_row24_traceSegment_035_0594_0009, g32p_row24_traceSegment_035_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 576 18 18, g32p_row24_traceSegment_035_0576_0018, g32p_row24_traceSegment_035_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 612 9 9, g32p_row24_traceSegment_035_0612_0009, g32p_row24_traceSegment_035_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 639 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 630 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 630 9 9, g32p_row24_traceSegment_035_0630_0009, g32p_row24_traceSegment_035_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 612 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 612 18 18, g32p_row24_traceSegment_035_0612_0018, g32p_row24_traceSegment_035_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 576 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 576 36 36, g32p_row24_traceSegment_035_0576_0036, g32p_row24_traceSegment_035_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 648 9 9, g32p_row24_traceSegment_035_0648_0009, g32p_row24_traceSegment_035_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 666 9 9, g32p_row24_traceSegment_035_0666_0009, g32p_row24_traceSegment_035_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 648 18 18, g32p_row24_traceSegment_035_0648_0018, g32p_row24_traceSegment_035_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 684 9 9, g32p_row24_traceSegment_035_0684_0009, g32p_row24_traceSegment_035_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 702 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 702 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 702 9 9, g32p_row24_traceSegment_035_0702_0009, g32p_row24_traceSegment_035_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 684 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 684 18 18, g32p_row24_traceSegment_035_0684_0018, g32p_row24_traceSegment_035_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 648 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 648 36 36, g32p_row24_traceSegment_035_0648_0036, g32p_row24_traceSegment_035_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 576 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 576 72 72, g32p_row24_traceSegment_035_0576_0072, g32p_row24_traceSegment_035_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 720 9 9, g32p_row24_traceSegment_035_0720_0009, g32p_row24_traceSegment_035_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 738 9 9, g32p_row24_traceSegment_035_0738_0009, g32p_row24_traceSegment_035_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 720 18 18, g32p_row24_traceSegment_035_0720_0018, g32p_row24_traceSegment_035_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 756 9 9, g32p_row24_traceSegment_035_0756_0009, g32p_row24_traceSegment_035_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 774 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 774 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 774 9 9, g32p_row24_traceSegment_035_0774_0009, g32p_row24_traceSegment_035_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 756 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 756 18 18, g32p_row24_traceSegment_035_0756_0018, g32p_row24_traceSegment_035_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 720 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 720 36 36, g32p_row24_traceSegment_035_0720_0036, g32p_row24_traceSegment_035_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 792 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 792 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 792 9 9, g32p_row24_traceSegment_035_0792_0009, g32p_row24_traceSegment_035_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 810 9 9, g32p_row24_traceSegment_035_0810_0009, g32p_row24_traceSegment_035_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 792 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 792 18 18, g32p_row24_traceSegment_035_0792_0018, g32p_row24_traceSegment_035_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 828 9 9, g32p_row24_traceSegment_035_0828_0009, g32p_row24_traceSegment_035_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 846 9 9, g32p_row24_traceSegment_035_0846_0009, g32p_row24_traceSegment_035_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 828 18 18, g32p_row24_traceSegment_035_0828_0018, g32p_row24_traceSegment_035_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 792 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 792 36 36, g32p_row24_traceSegment_035_0792_0036, g32p_row24_traceSegment_035_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 720 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 720 72 72, g32p_row24_traceSegment_035_0720_0072, g32p_row24_traceSegment_035_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_035 576 288 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 576 144 144, g32p_row24_traceSegment_035_0576_0144, g32p_row24_traceSegment_035_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 864 9 9, g32p_row24_traceSegment_035_0864_0009, g32p_row24_traceSegment_035_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 882 9 9, g32p_row24_traceSegment_035_0882_0009, g32p_row24_traceSegment_035_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 864 18 18, g32p_row24_traceSegment_035_0864_0018, g32p_row24_traceSegment_035_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 900 9 9, g32p_row24_traceSegment_035_0900_0009, g32p_row24_traceSegment_035_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 918 9 9, g32p_row24_traceSegment_035_0918_0009, g32p_row24_traceSegment_035_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 900 18 18, g32p_row24_traceSegment_035_0900_0018, g32p_row24_traceSegment_035_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 864 36 36, g32p_row24_traceSegment_035_0864_0036, g32p_row24_traceSegment_035_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 936 9 9, g32p_row24_traceSegment_035_0936_0009, g32p_row24_traceSegment_035_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 954 9 9, g32p_row24_traceSegment_035_0954_0009, g32p_row24_traceSegment_035_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 936 18 18, g32p_row24_traceSegment_035_0936_0018, g32p_row24_traceSegment_035_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 972 9 9, g32p_row24_traceSegment_035_0972_0009, g32p_row24_traceSegment_035_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 990 9 9, g32p_row24_traceSegment_035_0990_0009, g32p_row24_traceSegment_035_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 972 18 18, g32p_row24_traceSegment_035_0972_0018, g32p_row24_traceSegment_035_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 936 36 36, g32p_row24_traceSegment_035_0936_0036, g32p_row24_traceSegment_035_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 864 72 72, g32p_row24_traceSegment_035_0864_0072, g32p_row24_traceSegment_035_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1008 9 9, g32p_row24_traceSegment_035_1008_0009, g32p_row24_traceSegment_035_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1026 9 9, g32p_row24_traceSegment_035_1026_0009, g32p_row24_traceSegment_035_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1008 18 18, g32p_row24_traceSegment_035_1008_0018, g32p_row24_traceSegment_035_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1053 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1044 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1044 9 9, g32p_row24_traceSegment_035_1044_0009, g32p_row24_traceSegment_035_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1062 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1071 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1062 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1062 9 9, g32p_row24_traceSegment_035_1062_0009, g32p_row24_traceSegment_035_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 1044 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1044 18 18, g32p_row24_traceSegment_035_1044_0018, g32p_row24_traceSegment_035_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 1008 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1008 36 36, g32p_row24_traceSegment_035_1008_0036, g32p_row24_traceSegment_035_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1080 9 9, g32p_row24_traceSegment_035_1080_0009, g32p_row24_traceSegment_035_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1098 9 9, g32p_row24_traceSegment_035_1098_0009, g32p_row24_traceSegment_035_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1080 18 18, g32p_row24_traceSegment_035_1080_0018, g32p_row24_traceSegment_035_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1116 9 9, g32p_row24_traceSegment_035_1116_0009, g32p_row24_traceSegment_035_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_035 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_035_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_035 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1134 9 9, g32p_row24_traceSegment_035_1134_0009, g32p_row24_traceSegment_035_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_035 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1116 18 18, g32p_row24_traceSegment_035_1116_0018, g32p_row24_traceSegment_035_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_035 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1080 36 36, g32p_row24_traceSegment_035_1080_0036, g32p_row24_traceSegment_035_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_035_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_035 1008 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 1008 72 72, g32p_row24_traceSegment_035_1008_0072, g32p_row24_traceSegment_035_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_035 864 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 864 144 144, g32p_row24_traceSegment_035_0864_0144, g32p_row24_traceSegment_035_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_035 576 576 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 576 288 288, g32p_row24_traceSegment_035_0576_0288, g32p_row24_traceSegment_035_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_035_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_035 0 1152 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_035 0 576 576, g32p_row24_traceSegment_035_0000_0576, g32p_row24_traceSegment_035_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 35 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_035_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_037_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 9 9, g32p_row24_traceSegment_037_0000_0009, g32p_row24_traceSegment_037_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 18 9 9, g32p_row24_traceSegment_037_0018_0009, g32p_row24_traceSegment_037_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 18 18, g32p_row24_traceSegment_037_0000_0018, g32p_row24_traceSegment_037_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 36 9 9, g32p_row24_traceSegment_037_0036_0009, g32p_row24_traceSegment_037_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 54 9 9, g32p_row24_traceSegment_037_0054_0009, g32p_row24_traceSegment_037_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 36 18 18, g32p_row24_traceSegment_037_0036_0018, g32p_row24_traceSegment_037_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 36 36, g32p_row24_traceSegment_037_0000_0036, g32p_row24_traceSegment_037_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 72 9 9, g32p_row24_traceSegment_037_0072_0009, g32p_row24_traceSegment_037_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 90 9 9, g32p_row24_traceSegment_037_0090_0009, g32p_row24_traceSegment_037_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 72 18 18, g32p_row24_traceSegment_037_0072_0018, g32p_row24_traceSegment_037_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 108 9 9, g32p_row24_traceSegment_037_0108_0009, g32p_row24_traceSegment_037_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 126 9 9, g32p_row24_traceSegment_037_0126_0009, g32p_row24_traceSegment_037_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 108 18 18, g32p_row24_traceSegment_037_0108_0018, g32p_row24_traceSegment_037_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 72 36 36, g32p_row24_traceSegment_037_0072_0036, g32p_row24_traceSegment_037_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 72 72, g32p_row24_traceSegment_037_0000_0072, g32p_row24_traceSegment_037_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 144 9 9, g32p_row24_traceSegment_037_0144_0009, g32p_row24_traceSegment_037_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 162 9 9, g32p_row24_traceSegment_037_0162_0009, g32p_row24_traceSegment_037_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 144 18 18, g32p_row24_traceSegment_037_0144_0018, g32p_row24_traceSegment_037_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 180 9 9, g32p_row24_traceSegment_037_0180_0009, g32p_row24_traceSegment_037_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 198 9 9, g32p_row24_traceSegment_037_0198_0009, g32p_row24_traceSegment_037_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 180 18 18, g32p_row24_traceSegment_037_0180_0018, g32p_row24_traceSegment_037_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 144 36 36, g32p_row24_traceSegment_037_0144_0036, g32p_row24_traceSegment_037_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 216 9 9, g32p_row24_traceSegment_037_0216_0009, g32p_row24_traceSegment_037_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 234 9 9, g32p_row24_traceSegment_037_0234_0009, g32p_row24_traceSegment_037_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 216 18 18, g32p_row24_traceSegment_037_0216_0018, g32p_row24_traceSegment_037_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 252 9 9, g32p_row24_traceSegment_037_0252_0009, g32p_row24_traceSegment_037_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 270 9 9, g32p_row24_traceSegment_037_0270_0009, g32p_row24_traceSegment_037_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 252 18 18, g32p_row24_traceSegment_037_0252_0018, g32p_row24_traceSegment_037_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 216 36 36, g32p_row24_traceSegment_037_0216_0036, g32p_row24_traceSegment_037_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 144 72 72, g32p_row24_traceSegment_037_0144_0072, g32p_row24_traceSegment_037_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_037 0 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 144 144, g32p_row24_traceSegment_037_0000_0144, g32p_row24_traceSegment_037_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 288 9 9, g32p_row24_traceSegment_037_0288_0009, g32p_row24_traceSegment_037_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 306 9 9, g32p_row24_traceSegment_037_0306_0009, g32p_row24_traceSegment_037_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 288 18 18, g32p_row24_traceSegment_037_0288_0018, g32p_row24_traceSegment_037_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 324 9 9, g32p_row24_traceSegment_037_0324_0009, g32p_row24_traceSegment_037_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 342 9 9, g32p_row24_traceSegment_037_0342_0009, g32p_row24_traceSegment_037_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 324 18 18, g32p_row24_traceSegment_037_0324_0018, g32p_row24_traceSegment_037_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 288 36 36, g32p_row24_traceSegment_037_0288_0036, g32p_row24_traceSegment_037_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 360 9 9, g32p_row24_traceSegment_037_0360_0009, g32p_row24_traceSegment_037_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 378 9 9, g32p_row24_traceSegment_037_0378_0009, g32p_row24_traceSegment_037_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 360 18 18, g32p_row24_traceSegment_037_0360_0018, g32p_row24_traceSegment_037_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 396 9 9, g32p_row24_traceSegment_037_0396_0009, g32p_row24_traceSegment_037_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 414 9 9, g32p_row24_traceSegment_037_0414_0009, g32p_row24_traceSegment_037_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 396 18 18, g32p_row24_traceSegment_037_0396_0018, g32p_row24_traceSegment_037_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 360 36 36, g32p_row24_traceSegment_037_0360_0036, g32p_row24_traceSegment_037_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 288 72 72, g32p_row24_traceSegment_037_0288_0072, g32p_row24_traceSegment_037_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 432 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 432 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 432 9 9, g32p_row24_traceSegment_037_0432_0009, g32p_row24_traceSegment_037_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 450 9 9, g32p_row24_traceSegment_037_0450_0009, g32p_row24_traceSegment_037_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 432 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 432 18 18, g32p_row24_traceSegment_037_0432_0018, g32p_row24_traceSegment_037_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 468 9 9, g32p_row24_traceSegment_037_0468_0009, g32p_row24_traceSegment_037_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 486 9 9, g32p_row24_traceSegment_037_0486_0009, g32p_row24_traceSegment_037_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 468 18 18, g32p_row24_traceSegment_037_0468_0018, g32p_row24_traceSegment_037_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 432 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 432 36 36, g32p_row24_traceSegment_037_0432_0036, g32p_row24_traceSegment_037_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 504 9 9, g32p_row24_traceSegment_037_0504_0009, g32p_row24_traceSegment_037_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 522 9 9, g32p_row24_traceSegment_037_0522_0009, g32p_row24_traceSegment_037_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 504 18 18, g32p_row24_traceSegment_037_0504_0018, g32p_row24_traceSegment_037_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 540 9 9, g32p_row24_traceSegment_037_0540_0009, g32p_row24_traceSegment_037_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 558 9 9, g32p_row24_traceSegment_037_0558_0009, g32p_row24_traceSegment_037_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 540 18 18, g32p_row24_traceSegment_037_0540_0018, g32p_row24_traceSegment_037_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 504 36 36, g32p_row24_traceSegment_037_0504_0036, g32p_row24_traceSegment_037_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 432 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 432 72 72, g32p_row24_traceSegment_037_0432_0072, g32p_row24_traceSegment_037_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_037 288 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 288 144 144, g32p_row24_traceSegment_037_0288_0144, g32p_row24_traceSegment_037_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_037 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 288 288, g32p_row24_traceSegment_037_0000_0288, g32p_row24_traceSegment_037_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 576 9 9, g32p_row24_traceSegment_037_0576_0009, g32p_row24_traceSegment_037_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 594 9 9, g32p_row24_traceSegment_037_0594_0009, g32p_row24_traceSegment_037_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 576 18 18, g32p_row24_traceSegment_037_0576_0018, g32p_row24_traceSegment_037_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 612 9 9, g32p_row24_traceSegment_037_0612_0009, g32p_row24_traceSegment_037_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 630 9 9, g32p_row24_traceSegment_037_0630_0009, g32p_row24_traceSegment_037_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 612 18 18, g32p_row24_traceSegment_037_0612_0018, g32p_row24_traceSegment_037_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 576 36 36, g32p_row24_traceSegment_037_0576_0036, g32p_row24_traceSegment_037_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 648 9 9, g32p_row24_traceSegment_037_0648_0009, g32p_row24_traceSegment_037_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 666 9 9, g32p_row24_traceSegment_037_0666_0009, g32p_row24_traceSegment_037_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 648 18 18, g32p_row24_traceSegment_037_0648_0018, g32p_row24_traceSegment_037_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 684 9 9, g32p_row24_traceSegment_037_0684_0009, g32p_row24_traceSegment_037_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 702 9 9, g32p_row24_traceSegment_037_0702_0009, g32p_row24_traceSegment_037_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 684 18 18, g32p_row24_traceSegment_037_0684_0018, g32p_row24_traceSegment_037_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 648 36 36, g32p_row24_traceSegment_037_0648_0036, g32p_row24_traceSegment_037_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 576 72 72, g32p_row24_traceSegment_037_0576_0072, g32p_row24_traceSegment_037_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 720 9 9, g32p_row24_traceSegment_037_0720_0009, g32p_row24_traceSegment_037_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 738 9 9, g32p_row24_traceSegment_037_0738_0009, g32p_row24_traceSegment_037_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 720 18 18, g32p_row24_traceSegment_037_0720_0018, g32p_row24_traceSegment_037_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 756 9 9, g32p_row24_traceSegment_037_0756_0009, g32p_row24_traceSegment_037_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 774 9 9, g32p_row24_traceSegment_037_0774_0009, g32p_row24_traceSegment_037_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 756 18 18, g32p_row24_traceSegment_037_0756_0018, g32p_row24_traceSegment_037_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 720 36 36, g32p_row24_traceSegment_037_0720_0036, g32p_row24_traceSegment_037_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 792 9 9, g32p_row24_traceSegment_037_0792_0009, g32p_row24_traceSegment_037_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 810 9 9, g32p_row24_traceSegment_037_0810_0009, g32p_row24_traceSegment_037_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 792 18 18, g32p_row24_traceSegment_037_0792_0018, g32p_row24_traceSegment_037_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 828 9 9, g32p_row24_traceSegment_037_0828_0009, g32p_row24_traceSegment_037_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 846 9 9, g32p_row24_traceSegment_037_0846_0009, g32p_row24_traceSegment_037_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 828 18 18, g32p_row24_traceSegment_037_0828_0018, g32p_row24_traceSegment_037_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 792 36 36, g32p_row24_traceSegment_037_0792_0036, g32p_row24_traceSegment_037_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 720 72 72, g32p_row24_traceSegment_037_0720_0072, g32p_row24_traceSegment_037_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_037 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 576 144 144, g32p_row24_traceSegment_037_0576_0144, g32p_row24_traceSegment_037_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 864 9 9, g32p_row24_traceSegment_037_0864_0009, g32p_row24_traceSegment_037_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 882 9 9, g32p_row24_traceSegment_037_0882_0009, g32p_row24_traceSegment_037_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 864 18 18, g32p_row24_traceSegment_037_0864_0018, g32p_row24_traceSegment_037_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 900 9 9, g32p_row24_traceSegment_037_0900_0009, g32p_row24_traceSegment_037_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 918 9 9, g32p_row24_traceSegment_037_0918_0009, g32p_row24_traceSegment_037_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 900 18 18, g32p_row24_traceSegment_037_0900_0018, g32p_row24_traceSegment_037_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 864 36 36, g32p_row24_traceSegment_037_0864_0036, g32p_row24_traceSegment_037_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 936 9 9, g32p_row24_traceSegment_037_0936_0009, g32p_row24_traceSegment_037_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 954 9 9, g32p_row24_traceSegment_037_0954_0009, g32p_row24_traceSegment_037_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 936 18 18, g32p_row24_traceSegment_037_0936_0018, g32p_row24_traceSegment_037_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 972 9 9, g32p_row24_traceSegment_037_0972_0009, g32p_row24_traceSegment_037_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 990 9 9, g32p_row24_traceSegment_037_0990_0009, g32p_row24_traceSegment_037_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 972 18 18, g32p_row24_traceSegment_037_0972_0018, g32p_row24_traceSegment_037_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 936 36 36, g32p_row24_traceSegment_037_0936_0036, g32p_row24_traceSegment_037_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 864 72 72, g32p_row24_traceSegment_037_0864_0072, g32p_row24_traceSegment_037_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1008 9 9, g32p_row24_traceSegment_037_1008_0009, g32p_row24_traceSegment_037_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1026 9 9, g32p_row24_traceSegment_037_1026_0009, g32p_row24_traceSegment_037_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1008 18 18, g32p_row24_traceSegment_037_1008_0018, g32p_row24_traceSegment_037_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1044 9 9, g32p_row24_traceSegment_037_1044_0009, g32p_row24_traceSegment_037_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1062 9 9, g32p_row24_traceSegment_037_1062_0009, g32p_row24_traceSegment_037_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1044 18 18, g32p_row24_traceSegment_037_1044_0018, g32p_row24_traceSegment_037_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1008 36 36, g32p_row24_traceSegment_037_1008_0036, g32p_row24_traceSegment_037_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1080 9 9, g32p_row24_traceSegment_037_1080_0009, g32p_row24_traceSegment_037_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1098 9 9, g32p_row24_traceSegment_037_1098_0009, g32p_row24_traceSegment_037_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1080 18 18, g32p_row24_traceSegment_037_1080_0018, g32p_row24_traceSegment_037_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1116 9 9, g32p_row24_traceSegment_037_1116_0009, g32p_row24_traceSegment_037_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_037 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_037_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_037 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1134 9 9, g32p_row24_traceSegment_037_1134_0009, g32p_row24_traceSegment_037_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_037 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1116 18 18, g32p_row24_traceSegment_037_1116_0018, g32p_row24_traceSegment_037_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_037 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1080 36 36, g32p_row24_traceSegment_037_1080_0036, g32p_row24_traceSegment_037_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_037_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_037 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 1008 72 72, g32p_row24_traceSegment_037_1008_0072, g32p_row24_traceSegment_037_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_037 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 864 144 144, g32p_row24_traceSegment_037_0864_0144, g32p_row24_traceSegment_037_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_037 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 576 288 288, g32p_row24_traceSegment_037_0576_0288, g32p_row24_traceSegment_037_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_037_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_037 0 1152 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_037 0 576 576, g32p_row24_traceSegment_037_0000_0576, g32p_row24_traceSegment_037_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_037_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_038_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 9 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 0 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 9 9, g32p_row24_traceSegment_038_0000_0009, g32p_row24_traceSegment_038_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 18 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 18 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 18 9 9, g32p_row24_traceSegment_038_0018_0009, g32p_row24_traceSegment_038_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 0 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 18 18, g32p_row24_traceSegment_038_0000_0018, g32p_row24_traceSegment_038_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 45 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 36 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 36 9 9, g32p_row24_traceSegment_038_0036_0009, g32p_row24_traceSegment_038_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 63 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 54 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 54 9 9, g32p_row24_traceSegment_038_0054_0009, g32p_row24_traceSegment_038_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 36 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 36 18 18, g32p_row24_traceSegment_038_0036_0018, g32p_row24_traceSegment_038_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 0 72 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 36 36, g32p_row24_traceSegment_038_0000_0036, g32p_row24_traceSegment_038_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 72 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 72 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 72 9 9, g32p_row24_traceSegment_038_0072_0009, g32p_row24_traceSegment_038_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 90 9 9, g32p_row24_traceSegment_038_0090_0009, g32p_row24_traceSegment_038_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 72 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 72 18 18, g32p_row24_traceSegment_038_0072_0018, g32p_row24_traceSegment_038_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 117 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 108 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 108 9 9, g32p_row24_traceSegment_038_0108_0009, g32p_row24_traceSegment_038_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 126 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 135 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 126 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 126 9 9, g32p_row24_traceSegment_038_0126_0009, g32p_row24_traceSegment_038_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 108 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 108 18 18, g32p_row24_traceSegment_038_0108_0018, g32p_row24_traceSegment_038_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 72 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 72 36 36, g32p_row24_traceSegment_038_0072_0036, g32p_row24_traceSegment_038_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 0 144 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 72 72, g32p_row24_traceSegment_038_0000_0072, g32p_row24_traceSegment_038_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 144 9 9, g32p_row24_traceSegment_038_0144_0009, g32p_row24_traceSegment_038_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 162 9 9, g32p_row24_traceSegment_038_0162_0009, g32p_row24_traceSegment_038_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 144 18 18, g32p_row24_traceSegment_038_0144_0018, g32p_row24_traceSegment_038_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 180 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 189 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 180 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 180 9 9, g32p_row24_traceSegment_038_0180_0009, g32p_row24_traceSegment_038_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 198 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 207 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 198 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 198 9 9, g32p_row24_traceSegment_038_0198_0009, g32p_row24_traceSegment_038_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 180 36 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 180 18 18, g32p_row24_traceSegment_038_0180_0018, g32p_row24_traceSegment_038_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 144 72 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 144 36 36, g32p_row24_traceSegment_038_0144_0036, g32p_row24_traceSegment_038_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 225 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 216 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 216 9 9, g32p_row24_traceSegment_038_0216_0009, g32p_row24_traceSegment_038_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 243 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 234 9 9, g32p_row24_traceSegment_038_0234_0009, g32p_row24_traceSegment_038_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 216 36 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 216 18 18, g32p_row24_traceSegment_038_0216_0018, g32p_row24_traceSegment_038_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 252 9 9, g32p_row24_traceSegment_038_0252_0009, g32p_row24_traceSegment_038_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 279 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 270 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 270 9 9, g32p_row24_traceSegment_038_0270_0009, g32p_row24_traceSegment_038_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 252 18 18, g32p_row24_traceSegment_038_0252_0018, g32p_row24_traceSegment_038_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 216 72 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 216 36 36, g32p_row24_traceSegment_038_0216_0036, g32p_row24_traceSegment_038_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 144 144 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 144 72 72, g32p_row24_traceSegment_038_0144_0072, g32p_row24_traceSegment_038_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_038 0 288 = [0, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 144 144, g32p_row24_traceSegment_038_0000_0144, g32p_row24_traceSegment_038_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 288 9 9, g32p_row24_traceSegment_038_0288_0009, g32p_row24_traceSegment_038_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 306 9 9, g32p_row24_traceSegment_038_0306_0009, g32p_row24_traceSegment_038_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 288 18 18, g32p_row24_traceSegment_038_0288_0018, g32p_row24_traceSegment_038_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 324 9 9, g32p_row24_traceSegment_038_0324_0009, g32p_row24_traceSegment_038_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 342 9 9, g32p_row24_traceSegment_038_0342_0009, g32p_row24_traceSegment_038_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 324 18 18, g32p_row24_traceSegment_038_0324_0018, g32p_row24_traceSegment_038_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 288 36 36, g32p_row24_traceSegment_038_0288_0036, g32p_row24_traceSegment_038_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 360 9 9, g32p_row24_traceSegment_038_0360_0009, g32p_row24_traceSegment_038_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 378 9 9, g32p_row24_traceSegment_038_0378_0009, g32p_row24_traceSegment_038_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 360 18 18, g32p_row24_traceSegment_038_0360_0018, g32p_row24_traceSegment_038_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 396 9 9, g32p_row24_traceSegment_038_0396_0009, g32p_row24_traceSegment_038_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 414 9 9, g32p_row24_traceSegment_038_0414_0009, g32p_row24_traceSegment_038_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 396 18 18, g32p_row24_traceSegment_038_0396_0018, g32p_row24_traceSegment_038_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 360 36 36, g32p_row24_traceSegment_038_0360_0036, g32p_row24_traceSegment_038_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 288 72 72, g32p_row24_traceSegment_038_0288_0072, g32p_row24_traceSegment_038_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 432 9 9, g32p_row24_traceSegment_038_0432_0009, g32p_row24_traceSegment_038_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 450 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 459 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 450 18 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 450 9 9, g32p_row24_traceSegment_038_0450_0009, g32p_row24_traceSegment_038_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 432 36 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 432 18 18, g32p_row24_traceSegment_038_0432_0018, g32p_row24_traceSegment_038_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 468 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 477 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 468 18 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 468 9 9, g32p_row24_traceSegment_038_0468_0009, g32p_row24_traceSegment_038_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 486 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 495 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 486 18 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 486 9 9, g32p_row24_traceSegment_038_0486_0009, g32p_row24_traceSegment_038_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 468 36 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 468 18 18, g32p_row24_traceSegment_038_0468_0018, g32p_row24_traceSegment_038_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 432 72 = [0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 432 36 36, g32p_row24_traceSegment_038_0432_0036, g32p_row24_traceSegment_038_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 504 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 513 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 504 18 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 504 9 9, g32p_row24_traceSegment_038_0504_0009, g32p_row24_traceSegment_038_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 522 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 531 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 522 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 522 9 9, g32p_row24_traceSegment_038_0522_0009, g32p_row24_traceSegment_038_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 504 36 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 504 18 18, g32p_row24_traceSegment_038_0504_0018, g32p_row24_traceSegment_038_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 540 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 549 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 540 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 540 9 9, g32p_row24_traceSegment_038_0540_0009, g32p_row24_traceSegment_038_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 558 9 9, g32p_row24_traceSegment_038_0558_0009, g32p_row24_traceSegment_038_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 540 36 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 540 18 18, g32p_row24_traceSegment_038_0540_0018, g32p_row24_traceSegment_038_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 504 72 = [0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 504 36 36, g32p_row24_traceSegment_038_0504_0036, g32p_row24_traceSegment_038_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 432 144 = [0, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 432 72 72, g32p_row24_traceSegment_038_0432_0072, g32p_row24_traceSegment_038_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_038 288 288 = [0, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 288 144 144, g32p_row24_traceSegment_038_0288_0144, g32p_row24_traceSegment_038_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_038 0 576 = [0, 0, 0, 61] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 288 288, g32p_row24_traceSegment_038_0000_0288, g32p_row24_traceSegment_038_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 576 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 585 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 576 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 576 9 9, g32p_row24_traceSegment_038_0576_0009, g32p_row24_traceSegment_038_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 594 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 594 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 594 9 9, g32p_row24_traceSegment_038_0594_0009, g32p_row24_traceSegment_038_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 576 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 576 18 18, g32p_row24_traceSegment_038_0576_0018, g32p_row24_traceSegment_038_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 621 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 612 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 612 9 9, g32p_row24_traceSegment_038_0612_0009, g32p_row24_traceSegment_038_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 630 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 639 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 630 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 630 9 9, g32p_row24_traceSegment_038_0630_0009, g32p_row24_traceSegment_038_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 612 36 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 612 18 18, g32p_row24_traceSegment_038_0612_0018, g32p_row24_traceSegment_038_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 576 72 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 576 36 36, g32p_row24_traceSegment_038_0576_0036, g32p_row24_traceSegment_038_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 657 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 648 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 648 9 9, g32p_row24_traceSegment_038_0648_0009, g32p_row24_traceSegment_038_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 666 9 9, g32p_row24_traceSegment_038_0666_0009, g32p_row24_traceSegment_038_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 648 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 648 18 18, g32p_row24_traceSegment_038_0648_0018, g32p_row24_traceSegment_038_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 684 9 9, g32p_row24_traceSegment_038_0684_0009, g32p_row24_traceSegment_038_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 711 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 702 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 702 9 9, g32p_row24_traceSegment_038_0702_0009, g32p_row24_traceSegment_038_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 684 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 684 18 18, g32p_row24_traceSegment_038_0684_0018, g32p_row24_traceSegment_038_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 648 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 648 36 36, g32p_row24_traceSegment_038_0648_0036, g32p_row24_traceSegment_038_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 576 144 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 576 72 72, g32p_row24_traceSegment_038_0576_0072, g32p_row24_traceSegment_038_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 720 9 9, g32p_row24_traceSegment_038_0720_0009, g32p_row24_traceSegment_038_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 738 9 9, g32p_row24_traceSegment_038_0738_0009, g32p_row24_traceSegment_038_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 720 18 18, g32p_row24_traceSegment_038_0720_0018, g32p_row24_traceSegment_038_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 756 9 9, g32p_row24_traceSegment_038_0756_0009, g32p_row24_traceSegment_038_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 774 9 9, g32p_row24_traceSegment_038_0774_0009, g32p_row24_traceSegment_038_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 756 18 18, g32p_row24_traceSegment_038_0756_0018, g32p_row24_traceSegment_038_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 720 36 36, g32p_row24_traceSegment_038_0720_0036, g32p_row24_traceSegment_038_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 792 9 9, g32p_row24_traceSegment_038_0792_0009, g32p_row24_traceSegment_038_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 810 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 819 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 810 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 810 9 9, g32p_row24_traceSegment_038_0810_0009, g32p_row24_traceSegment_038_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 792 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 792 18 18, g32p_row24_traceSegment_038_0792_0018, g32p_row24_traceSegment_038_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 828 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 837 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 828 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 828 9 9, g32p_row24_traceSegment_038_0828_0009, g32p_row24_traceSegment_038_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 846 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 855 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 846 18 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 846 9 9, g32p_row24_traceSegment_038_0846_0009, g32p_row24_traceSegment_038_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 828 36 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 828 18 18, g32p_row24_traceSegment_038_0828_0018, g32p_row24_traceSegment_038_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 792 72 = [0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 792 36 36, g32p_row24_traceSegment_038_0792_0036, g32p_row24_traceSegment_038_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 720 144 = [0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 720 72 72, g32p_row24_traceSegment_038_0720_0072, g32p_row24_traceSegment_038_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_038 576 288 = [0, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 576 144 144, g32p_row24_traceSegment_038_0576_0144, g32p_row24_traceSegment_038_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 864 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 873 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 864 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 864 9 9, g32p_row24_traceSegment_038_0864_0009, g32p_row24_traceSegment_038_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 882 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 891 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 882 18 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 882 9 9, g32p_row24_traceSegment_038_0882_0009, g32p_row24_traceSegment_038_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 864 36 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 864 18 18, g32p_row24_traceSegment_038_0864_0018, g32p_row24_traceSegment_038_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 900 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 909 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 900 18 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 900 9 9, g32p_row24_traceSegment_038_0900_0009, g32p_row24_traceSegment_038_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 918 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 927 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 918 18 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 918 9 9, g32p_row24_traceSegment_038_0918_0009, g32p_row24_traceSegment_038_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 900 36 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 900 18 18, g32p_row24_traceSegment_038_0900_0018, g32p_row24_traceSegment_038_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 864 72 = [0, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 864 36 36, g32p_row24_traceSegment_038_0864_0036, g32p_row24_traceSegment_038_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 936 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 945 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 936 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 936 9 9, g32p_row24_traceSegment_038_0936_0009, g32p_row24_traceSegment_038_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 963 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 954 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 954 9 9, g32p_row24_traceSegment_038_0954_0009, g32p_row24_traceSegment_038_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 936 36 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 936 18 18, g32p_row24_traceSegment_038_0936_0018, g32p_row24_traceSegment_038_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 972 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 981 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 972 18 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 972 9 9, g32p_row24_traceSegment_038_0972_0009, g32p_row24_traceSegment_038_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 990 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 999 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 990 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 990 9 9, g32p_row24_traceSegment_038_0990_0009, g32p_row24_traceSegment_038_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 972 36 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 972 18 18, g32p_row24_traceSegment_038_0972_0018, g32p_row24_traceSegment_038_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 936 72 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 936 36 36, g32p_row24_traceSegment_038_0936_0036, g32p_row24_traceSegment_038_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 864 144 = [0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 864 72 72, g32p_row24_traceSegment_038_0864_0072, g32p_row24_traceSegment_038_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1008 9 9, g32p_row24_traceSegment_038_1008_0009, g32p_row24_traceSegment_038_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1035 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1026 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1026 9 9, g32p_row24_traceSegment_038_1026_0009, g32p_row24_traceSegment_038_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 1008 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1008 18 18, g32p_row24_traceSegment_038_1008_0018, g32p_row24_traceSegment_038_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1053 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1044 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1044 9 9, g32p_row24_traceSegment_038_1044_0009, g32p_row24_traceSegment_038_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1062 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1062 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1062 9 9, g32p_row24_traceSegment_038_1062_0009, g32p_row24_traceSegment_038_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 1044 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1044 18 18, g32p_row24_traceSegment_038_1044_0018, g32p_row24_traceSegment_038_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 1008 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1008 36 36, g32p_row24_traceSegment_038_1008_0036, g32p_row24_traceSegment_038_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1080 9 9, g32p_row24_traceSegment_038_1080_0009, g32p_row24_traceSegment_038_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1098 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1107 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1098 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1098 9 9, g32p_row24_traceSegment_038_1098_0009, g32p_row24_traceSegment_038_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 1080 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1080 18 18, g32p_row24_traceSegment_038_1080_0018, g32p_row24_traceSegment_038_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1116 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1125 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1116 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1116 9 9, g32p_row24_traceSegment_038_1116_0009, g32p_row24_traceSegment_038_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1134 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_038 1143 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_038_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_038 1134 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1134 9 9, g32p_row24_traceSegment_038_1134_0009, g32p_row24_traceSegment_038_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_038 1116 36 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1116 18 18, g32p_row24_traceSegment_038_1116_0018, g32p_row24_traceSegment_038_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_038 1080 72 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1080 36 36, g32p_row24_traceSegment_038_1080_0036, g32p_row24_traceSegment_038_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_038_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_038 1008 144 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 1008 72 72, g32p_row24_traceSegment_038_1008_0072, g32p_row24_traceSegment_038_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_038 864 288 = [0, 0, 0, 55] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 864 144 144, g32p_row24_traceSegment_038_0864_0144, g32p_row24_traceSegment_038_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_038 576 576 = [0, 0, 0, 83] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 576 288 288, g32p_row24_traceSegment_038_0576_0288, g32p_row24_traceSegment_038_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_038_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_038 0 1152 = [0, 0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_038 0 576 576, g32p_row24_traceSegment_038_0000_0576, g32p_row24_traceSegment_038_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 38 = [0, 0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_038_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_040 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 40 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_040_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 9 9, g32p_row24_traceSegment_040_0000_0009, g32p_row24_traceSegment_040_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 18 9 9, g32p_row24_traceSegment_040_0018_0009, g32p_row24_traceSegment_040_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 18 18, g32p_row24_traceSegment_040_0000_0018, g32p_row24_traceSegment_040_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 36 9 9, g32p_row24_traceSegment_040_0036_0009, g32p_row24_traceSegment_040_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 54 9 9, g32p_row24_traceSegment_040_0054_0009, g32p_row24_traceSegment_040_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 36 18 18, g32p_row24_traceSegment_040_0036_0018, g32p_row24_traceSegment_040_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 36 36, g32p_row24_traceSegment_040_0000_0036, g32p_row24_traceSegment_040_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 72 9 9, g32p_row24_traceSegment_040_0072_0009, g32p_row24_traceSegment_040_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 90 9 9, g32p_row24_traceSegment_040_0090_0009, g32p_row24_traceSegment_040_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 72 18 18, g32p_row24_traceSegment_040_0072_0018, g32p_row24_traceSegment_040_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 108 9 9, g32p_row24_traceSegment_040_0108_0009, g32p_row24_traceSegment_040_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 126 9 9, g32p_row24_traceSegment_040_0126_0009, g32p_row24_traceSegment_040_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 108 18 18, g32p_row24_traceSegment_040_0108_0018, g32p_row24_traceSegment_040_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 72 36 36, g32p_row24_traceSegment_040_0072_0036, g32p_row24_traceSegment_040_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 72 72, g32p_row24_traceSegment_040_0000_0072, g32p_row24_traceSegment_040_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 144 9 9, g32p_row24_traceSegment_040_0144_0009, g32p_row24_traceSegment_040_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 162 9 9, g32p_row24_traceSegment_040_0162_0009, g32p_row24_traceSegment_040_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 144 18 18, g32p_row24_traceSegment_040_0144_0018, g32p_row24_traceSegment_040_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 180 9 9, g32p_row24_traceSegment_040_0180_0009, g32p_row24_traceSegment_040_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 198 9 9, g32p_row24_traceSegment_040_0198_0009, g32p_row24_traceSegment_040_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 180 18 18, g32p_row24_traceSegment_040_0180_0018, g32p_row24_traceSegment_040_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 144 36 36, g32p_row24_traceSegment_040_0144_0036, g32p_row24_traceSegment_040_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 216 9 9, g32p_row24_traceSegment_040_0216_0009, g32p_row24_traceSegment_040_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 234 9 9, g32p_row24_traceSegment_040_0234_0009, g32p_row24_traceSegment_040_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 216 18 18, g32p_row24_traceSegment_040_0216_0018, g32p_row24_traceSegment_040_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 252 9 9, g32p_row24_traceSegment_040_0252_0009, g32p_row24_traceSegment_040_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 270 9 9, g32p_row24_traceSegment_040_0270_0009, g32p_row24_traceSegment_040_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 252 18 18, g32p_row24_traceSegment_040_0252_0018, g32p_row24_traceSegment_040_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 216 36 36, g32p_row24_traceSegment_040_0216_0036, g32p_row24_traceSegment_040_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 144 72 72, g32p_row24_traceSegment_040_0144_0072, g32p_row24_traceSegment_040_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_040 0 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 144 144, g32p_row24_traceSegment_040_0000_0144, g32p_row24_traceSegment_040_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 288 9 9, g32p_row24_traceSegment_040_0288_0009, g32p_row24_traceSegment_040_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 306 9 9, g32p_row24_traceSegment_040_0306_0009, g32p_row24_traceSegment_040_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 288 18 18, g32p_row24_traceSegment_040_0288_0018, g32p_row24_traceSegment_040_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 324 9 9, g32p_row24_traceSegment_040_0324_0009, g32p_row24_traceSegment_040_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 342 9 9, g32p_row24_traceSegment_040_0342_0009, g32p_row24_traceSegment_040_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 324 18 18, g32p_row24_traceSegment_040_0324_0018, g32p_row24_traceSegment_040_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 288 36 36, g32p_row24_traceSegment_040_0288_0036, g32p_row24_traceSegment_040_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 360 9 9, g32p_row24_traceSegment_040_0360_0009, g32p_row24_traceSegment_040_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 378 9 9, g32p_row24_traceSegment_040_0378_0009, g32p_row24_traceSegment_040_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 360 18 18, g32p_row24_traceSegment_040_0360_0018, g32p_row24_traceSegment_040_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 396 9 9, g32p_row24_traceSegment_040_0396_0009, g32p_row24_traceSegment_040_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 414 9 9, g32p_row24_traceSegment_040_0414_0009, g32p_row24_traceSegment_040_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 396 18 18, g32p_row24_traceSegment_040_0396_0018, g32p_row24_traceSegment_040_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 360 36 36, g32p_row24_traceSegment_040_0360_0036, g32p_row24_traceSegment_040_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 288 72 72, g32p_row24_traceSegment_040_0288_0072, g32p_row24_traceSegment_040_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 432 9 9, g32p_row24_traceSegment_040_0432_0009, g32p_row24_traceSegment_040_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 450 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 459 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 450 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 450 9 9, g32p_row24_traceSegment_040_0450_0009, g32p_row24_traceSegment_040_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 432 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 432 18 18, g32p_row24_traceSegment_040_0432_0018, g32p_row24_traceSegment_040_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 468 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 468 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 468 9 9, g32p_row24_traceSegment_040_0468_0009, g32p_row24_traceSegment_040_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 486 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 495 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 486 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 486 9 9, g32p_row24_traceSegment_040_0486_0009, g32p_row24_traceSegment_040_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 468 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 468 18 18, g32p_row24_traceSegment_040_0468_0018, g32p_row24_traceSegment_040_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 432 72 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 432 36 36, g32p_row24_traceSegment_040_0432_0036, g32p_row24_traceSegment_040_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 504 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 504 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 504 9 9, g32p_row24_traceSegment_040_0504_0009, g32p_row24_traceSegment_040_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 522 9 9, g32p_row24_traceSegment_040_0522_0009, g32p_row24_traceSegment_040_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 504 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 504 18 18, g32p_row24_traceSegment_040_0504_0018, g32p_row24_traceSegment_040_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 540 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 540 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 540 9 9, g32p_row24_traceSegment_040_0540_0009, g32p_row24_traceSegment_040_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 558 9 9, g32p_row24_traceSegment_040_0558_0009, g32p_row24_traceSegment_040_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 540 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 540 18 18, g32p_row24_traceSegment_040_0540_0018, g32p_row24_traceSegment_040_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 504 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 504 36 36, g32p_row24_traceSegment_040_0504_0036, g32p_row24_traceSegment_040_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 432 144 = [9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 432 72 72, g32p_row24_traceSegment_040_0432_0072, g32p_row24_traceSegment_040_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_040 288 288 = [9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 288 144 144, g32p_row24_traceSegment_040_0288_0144, g32p_row24_traceSegment_040_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_040 0 576 = [9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 288 288, g32p_row24_traceSegment_040_0000_0288, g32p_row24_traceSegment_040_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 576 9 9, g32p_row24_traceSegment_040_0576_0009, g32p_row24_traceSegment_040_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 594 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 594 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 594 9 9, g32p_row24_traceSegment_040_0594_0009, g32p_row24_traceSegment_040_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 576 18 18, g32p_row24_traceSegment_040_0576_0018, g32p_row24_traceSegment_040_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 612 9 9, g32p_row24_traceSegment_040_0612_0009, g32p_row24_traceSegment_040_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 630 9 9, g32p_row24_traceSegment_040_0630_0009, g32p_row24_traceSegment_040_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 612 18 18, g32p_row24_traceSegment_040_0612_0018, g32p_row24_traceSegment_040_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 576 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 576 36 36, g32p_row24_traceSegment_040_0576_0036, g32p_row24_traceSegment_040_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 648 9 9, g32p_row24_traceSegment_040_0648_0009, g32p_row24_traceSegment_040_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 666 9 9, g32p_row24_traceSegment_040_0666_0009, g32p_row24_traceSegment_040_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 648 18 18, g32p_row24_traceSegment_040_0648_0018, g32p_row24_traceSegment_040_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 684 9 9, g32p_row24_traceSegment_040_0684_0009, g32p_row24_traceSegment_040_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 702 9 9, g32p_row24_traceSegment_040_0702_0009, g32p_row24_traceSegment_040_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 684 18 18, g32p_row24_traceSegment_040_0684_0018, g32p_row24_traceSegment_040_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 648 36 36, g32p_row24_traceSegment_040_0648_0036, g32p_row24_traceSegment_040_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 576 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 576 72 72, g32p_row24_traceSegment_040_0576_0072, g32p_row24_traceSegment_040_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 720 9 9, g32p_row24_traceSegment_040_0720_0009, g32p_row24_traceSegment_040_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 738 9 9, g32p_row24_traceSegment_040_0738_0009, g32p_row24_traceSegment_040_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 720 18 18, g32p_row24_traceSegment_040_0720_0018, g32p_row24_traceSegment_040_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 756 9 9, g32p_row24_traceSegment_040_0756_0009, g32p_row24_traceSegment_040_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 774 9 9, g32p_row24_traceSegment_040_0774_0009, g32p_row24_traceSegment_040_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 756 18 18, g32p_row24_traceSegment_040_0756_0018, g32p_row24_traceSegment_040_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 720 36 36, g32p_row24_traceSegment_040_0720_0036, g32p_row24_traceSegment_040_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 792 9 9, g32p_row24_traceSegment_040_0792_0009, g32p_row24_traceSegment_040_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 810 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 819 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 810 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 810 9 9, g32p_row24_traceSegment_040_0810_0009, g32p_row24_traceSegment_040_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 792 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 792 18 18, g32p_row24_traceSegment_040_0792_0018, g32p_row24_traceSegment_040_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 837 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 828 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 828 9 9, g32p_row24_traceSegment_040_0828_0009, g32p_row24_traceSegment_040_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 846 9 = [3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 855 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 846 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 846 9 9, g32p_row24_traceSegment_040_0846_0009, g32p_row24_traceSegment_040_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 828 36 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 828 18 18, g32p_row24_traceSegment_040_0828_0018, g32p_row24_traceSegment_040_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 792 72 = [8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 792 36 36, g32p_row24_traceSegment_040_0792_0036, g32p_row24_traceSegment_040_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 720 144 = [8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 720 72 72, g32p_row24_traceSegment_040_0720_0072, g32p_row24_traceSegment_040_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_040 576 288 = [9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 576 144 144, g32p_row24_traceSegment_040_0576_0144, g32p_row24_traceSegment_040_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 864 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 873 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 864 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 864 9 9, g32p_row24_traceSegment_040_0864_0009, g32p_row24_traceSegment_040_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 882 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 891 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 882 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 882 9 9, g32p_row24_traceSegment_040_0882_0009, g32p_row24_traceSegment_040_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 864 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 864 18 18, g32p_row24_traceSegment_040_0864_0018, g32p_row24_traceSegment_040_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 900 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 900 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 900 9 9, g32p_row24_traceSegment_040_0900_0009, g32p_row24_traceSegment_040_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 918 9 9, g32p_row24_traceSegment_040_0918_0009, g32p_row24_traceSegment_040_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 900 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 900 18 18, g32p_row24_traceSegment_040_0900_0018, g32p_row24_traceSegment_040_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 864 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 864 36 36, g32p_row24_traceSegment_040_0864_0036, g32p_row24_traceSegment_040_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 936 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 945 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 936 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 936 9 9, g32p_row24_traceSegment_040_0936_0009, g32p_row24_traceSegment_040_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 963 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 954 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 954 9 9, g32p_row24_traceSegment_040_0954_0009, g32p_row24_traceSegment_040_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 936 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 936 18 18, g32p_row24_traceSegment_040_0936_0018, g32p_row24_traceSegment_040_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 981 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 972 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 972 9 9, g32p_row24_traceSegment_040_0972_0009, g32p_row24_traceSegment_040_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 990 9 9, g32p_row24_traceSegment_040_0990_0009, g32p_row24_traceSegment_040_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 972 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 972 18 18, g32p_row24_traceSegment_040_0972_0018, g32p_row24_traceSegment_040_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 936 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 936 36 36, g32p_row24_traceSegment_040_0936_0036, g32p_row24_traceSegment_040_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 864 144 = [10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 864 72 72, g32p_row24_traceSegment_040_0864_0072, g32p_row24_traceSegment_040_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1008 9 9, g32p_row24_traceSegment_040_1008_0009, g32p_row24_traceSegment_040_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1026 9 9, g32p_row24_traceSegment_040_1026_0009, g32p_row24_traceSegment_040_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1008 18 18, g32p_row24_traceSegment_040_1008_0018, g32p_row24_traceSegment_040_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1044 9 9, g32p_row24_traceSegment_040_1044_0009, g32p_row24_traceSegment_040_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1062 9 9, g32p_row24_traceSegment_040_1062_0009, g32p_row24_traceSegment_040_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1044 18 18, g32p_row24_traceSegment_040_1044_0018, g32p_row24_traceSegment_040_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1008 36 36, g32p_row24_traceSegment_040_1008_0036, g32p_row24_traceSegment_040_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1080 9 9, g32p_row24_traceSegment_040_1080_0009, g32p_row24_traceSegment_040_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1098 9 9, g32p_row24_traceSegment_040_1098_0009, g32p_row24_traceSegment_040_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1080 18 18, g32p_row24_traceSegment_040_1080_0018, g32p_row24_traceSegment_040_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1116 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1125 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1116 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1116 9 9, g32p_row24_traceSegment_040_1116_0009, g32p_row24_traceSegment_040_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1134 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_040 1143 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_040_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_040 1134 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1134 9 9, g32p_row24_traceSegment_040_1134_0009, g32p_row24_traceSegment_040_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_040 1116 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1116 18 18, g32p_row24_traceSegment_040_1116_0018, g32p_row24_traceSegment_040_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_040 1080 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1080 36 36, g32p_row24_traceSegment_040_1080_0036, g32p_row24_traceSegment_040_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_040_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_040 1008 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 1008 72 72, g32p_row24_traceSegment_040_1008_0072, g32p_row24_traceSegment_040_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_040 864 288 = [14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 864 144 144, g32p_row24_traceSegment_040_0864_0144, g32p_row24_traceSegment_040_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_040 576 576 = [23] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 576 288 288, g32p_row24_traceSegment_040_0576_0288, g32p_row24_traceSegment_040_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_040_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_040 0 1152 = [32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_040 0 576 576, g32p_row24_traceSegment_040_0000_0576, g32p_row24_traceSegment_040_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 40 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_040_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_045_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 9 9, g32p_row24_traceSegment_045_0000_0009, g32p_row24_traceSegment_045_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 18 9 9, g32p_row24_traceSegment_045_0018_0009, g32p_row24_traceSegment_045_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 18 18, g32p_row24_traceSegment_045_0000_0018, g32p_row24_traceSegment_045_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 36 9 9, g32p_row24_traceSegment_045_0036_0009, g32p_row24_traceSegment_045_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 54 9 9, g32p_row24_traceSegment_045_0054_0009, g32p_row24_traceSegment_045_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 36 18 18, g32p_row24_traceSegment_045_0036_0018, g32p_row24_traceSegment_045_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 36 36, g32p_row24_traceSegment_045_0000_0036, g32p_row24_traceSegment_045_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 72 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 81 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 72 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 72 9 9, g32p_row24_traceSegment_045_0072_0009, g32p_row24_traceSegment_045_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 90 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 90 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 90 9 9, g32p_row24_traceSegment_045_0090_0009, g32p_row24_traceSegment_045_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 72 36 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 72 18 18, g32p_row24_traceSegment_045_0072_0018, g32p_row24_traceSegment_045_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 108 9 9, g32p_row24_traceSegment_045_0108_0009, g32p_row24_traceSegment_045_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 126 9 9, g32p_row24_traceSegment_045_0126_0009, g32p_row24_traceSegment_045_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 108 18 18, g32p_row24_traceSegment_045_0108_0018, g32p_row24_traceSegment_045_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 72 72 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 72 36 36, g32p_row24_traceSegment_045_0072_0036, g32p_row24_traceSegment_045_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 0 144 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 72 72, g32p_row24_traceSegment_045_0000_0072, g32p_row24_traceSegment_045_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 144 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 144 9 9, g32p_row24_traceSegment_045_0144_0009, g32p_row24_traceSegment_045_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 162 9 9, g32p_row24_traceSegment_045_0162_0009, g32p_row24_traceSegment_045_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 144 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 144 18 18, g32p_row24_traceSegment_045_0144_0018, g32p_row24_traceSegment_045_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 180 9 9, g32p_row24_traceSegment_045_0180_0009, g32p_row24_traceSegment_045_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 207 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 198 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 198 9 9, g32p_row24_traceSegment_045_0198_0009, g32p_row24_traceSegment_045_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 180 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 180 18 18, g32p_row24_traceSegment_045_0180_0018, g32p_row24_traceSegment_045_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 144 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 144 36 36, g32p_row24_traceSegment_045_0144_0036, g32p_row24_traceSegment_045_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 216 9 9, g32p_row24_traceSegment_045_0216_0009, g32p_row24_traceSegment_045_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 243 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 234 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 234 9 9, g32p_row24_traceSegment_045_0234_0009, g32p_row24_traceSegment_045_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 216 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 216 18 18, g32p_row24_traceSegment_045_0216_0018, g32p_row24_traceSegment_045_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 252 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 252 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 252 9 9, g32p_row24_traceSegment_045_0252_0009, g32p_row24_traceSegment_045_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 270 9 9, g32p_row24_traceSegment_045_0270_0009, g32p_row24_traceSegment_045_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 252 18 18, g32p_row24_traceSegment_045_0252_0018, g32p_row24_traceSegment_045_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 216 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 216 36 36, g32p_row24_traceSegment_045_0216_0036, g32p_row24_traceSegment_045_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 144 144 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 144 72 72, g32p_row24_traceSegment_045_0144_0072, g32p_row24_traceSegment_045_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_045 0 288 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 144 144, g32p_row24_traceSegment_045_0000_0144, g32p_row24_traceSegment_045_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 297 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 288 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 288 9 9, g32p_row24_traceSegment_045_0288_0009, g32p_row24_traceSegment_045_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 306 9 9, g32p_row24_traceSegment_045_0306_0009, g32p_row24_traceSegment_045_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 288 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 288 18 18, g32p_row24_traceSegment_045_0288_0018, g32p_row24_traceSegment_045_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 324 9 9, g32p_row24_traceSegment_045_0324_0009, g32p_row24_traceSegment_045_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 342 9 9, g32p_row24_traceSegment_045_0342_0009, g32p_row24_traceSegment_045_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 324 18 18, g32p_row24_traceSegment_045_0324_0018, g32p_row24_traceSegment_045_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 288 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 288 36 36, g32p_row24_traceSegment_045_0288_0036, g32p_row24_traceSegment_045_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 360 9 9, g32p_row24_traceSegment_045_0360_0009, g32p_row24_traceSegment_045_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 378 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 378 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 378 9 9, g32p_row24_traceSegment_045_0378_0009, g32p_row24_traceSegment_045_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 360 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 360 18 18, g32p_row24_traceSegment_045_0360_0018, g32p_row24_traceSegment_045_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 396 9 9, g32p_row24_traceSegment_045_0396_0009, g32p_row24_traceSegment_045_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 414 9 9, g32p_row24_traceSegment_045_0414_0009, g32p_row24_traceSegment_045_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 396 18 18, g32p_row24_traceSegment_045_0396_0018, g32p_row24_traceSegment_045_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 360 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 360 36 36, g32p_row24_traceSegment_045_0360_0036, g32p_row24_traceSegment_045_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 288 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 288 72 72, g32p_row24_traceSegment_045_0288_0072, g32p_row24_traceSegment_045_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 432 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 441 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 432 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 432 9 9, g32p_row24_traceSegment_045_0432_0009, g32p_row24_traceSegment_045_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 450 9 9, g32p_row24_traceSegment_045_0450_0009, g32p_row24_traceSegment_045_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 432 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 432 18 18, g32p_row24_traceSegment_045_0432_0018, g32p_row24_traceSegment_045_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 468 9 9, g32p_row24_traceSegment_045_0468_0009, g32p_row24_traceSegment_045_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 486 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 486 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 486 9 9, g32p_row24_traceSegment_045_0486_0009, g32p_row24_traceSegment_045_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 468 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 468 18 18, g32p_row24_traceSegment_045_0468_0018, g32p_row24_traceSegment_045_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 432 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 432 36 36, g32p_row24_traceSegment_045_0432_0036, g32p_row24_traceSegment_045_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 504 9 9, g32p_row24_traceSegment_045_0504_0009, g32p_row24_traceSegment_045_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 522 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 522 9 9, g32p_row24_traceSegment_045_0522_0009, g32p_row24_traceSegment_045_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 504 18 18, g32p_row24_traceSegment_045_0504_0018, g32p_row24_traceSegment_045_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 540 9 9, g32p_row24_traceSegment_045_0540_0009, g32p_row24_traceSegment_045_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 558 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 558 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 558 9 9, g32p_row24_traceSegment_045_0558_0009, g32p_row24_traceSegment_045_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 540 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 540 18 18, g32p_row24_traceSegment_045_0540_0018, g32p_row24_traceSegment_045_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 504 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 504 36 36, g32p_row24_traceSegment_045_0504_0036, g32p_row24_traceSegment_045_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 432 144 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 432 72 72, g32p_row24_traceSegment_045_0432_0072, g32p_row24_traceSegment_045_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_045 288 288 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 288 144 144, g32p_row24_traceSegment_045_0288_0144, g32p_row24_traceSegment_045_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_045 0 576 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 288 288, g32p_row24_traceSegment_045_0000_0288, g32p_row24_traceSegment_045_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 576 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 576 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 576 9 9, g32p_row24_traceSegment_045_0576_0009, g32p_row24_traceSegment_045_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 594 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 594 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 594 9 9, g32p_row24_traceSegment_045_0594_0009, g32p_row24_traceSegment_045_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 576 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 576 18 18, g32p_row24_traceSegment_045_0576_0018, g32p_row24_traceSegment_045_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 621 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 612 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 612 9 9, g32p_row24_traceSegment_045_0612_0009, g32p_row24_traceSegment_045_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 630 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 630 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 630 9 9, g32p_row24_traceSegment_045_0630_0009, g32p_row24_traceSegment_045_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 612 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 612 18 18, g32p_row24_traceSegment_045_0612_0018, g32p_row24_traceSegment_045_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 576 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 576 36 36, g32p_row24_traceSegment_045_0576_0036, g32p_row24_traceSegment_045_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 657 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 648 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 648 9 9, g32p_row24_traceSegment_045_0648_0009, g32p_row24_traceSegment_045_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 675 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 666 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 666 9 9, g32p_row24_traceSegment_045_0666_0009, g32p_row24_traceSegment_045_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 648 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 648 18 18, g32p_row24_traceSegment_045_0648_0018, g32p_row24_traceSegment_045_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 684 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 684 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 684 9 9, g32p_row24_traceSegment_045_0684_0009, g32p_row24_traceSegment_045_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 711 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 702 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 702 9 9, g32p_row24_traceSegment_045_0702_0009, g32p_row24_traceSegment_045_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 684 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 684 18 18, g32p_row24_traceSegment_045_0684_0018, g32p_row24_traceSegment_045_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 648 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 648 36 36, g32p_row24_traceSegment_045_0648_0036, g32p_row24_traceSegment_045_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 576 144 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 576 72 72, g32p_row24_traceSegment_045_0576_0072, g32p_row24_traceSegment_045_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 729 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 720 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 720 9 9, g32p_row24_traceSegment_045_0720_0009, g32p_row24_traceSegment_045_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 738 9 9, g32p_row24_traceSegment_045_0738_0009, g32p_row24_traceSegment_045_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 720 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 720 18 18, g32p_row24_traceSegment_045_0720_0018, g32p_row24_traceSegment_045_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 765 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 756 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 756 9 9, g32p_row24_traceSegment_045_0756_0009, g32p_row24_traceSegment_045_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 774 9 9, g32p_row24_traceSegment_045_0774_0009, g32p_row24_traceSegment_045_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 756 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 756 18 18, g32p_row24_traceSegment_045_0756_0018, g32p_row24_traceSegment_045_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 720 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 720 36 36, g32p_row24_traceSegment_045_0720_0036, g32p_row24_traceSegment_045_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 792 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 792 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 792 9 9, g32p_row24_traceSegment_045_0792_0009, g32p_row24_traceSegment_045_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 810 9 9, g32p_row24_traceSegment_045_0810_0009, g32p_row24_traceSegment_045_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 792 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 792 18 18, g32p_row24_traceSegment_045_0792_0018, g32p_row24_traceSegment_045_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 828 9 9, g32p_row24_traceSegment_045_0828_0009, g32p_row24_traceSegment_045_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 846 9 9, g32p_row24_traceSegment_045_0846_0009, g32p_row24_traceSegment_045_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 828 18 18, g32p_row24_traceSegment_045_0828_0018, g32p_row24_traceSegment_045_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 792 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 792 36 36, g32p_row24_traceSegment_045_0792_0036, g32p_row24_traceSegment_045_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 720 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 720 72 72, g32p_row24_traceSegment_045_0720_0072, g32p_row24_traceSegment_045_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_045 576 288 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 576 144 144, g32p_row24_traceSegment_045_0576_0144, g32p_row24_traceSegment_045_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 864 9 9, g32p_row24_traceSegment_045_0864_0009, g32p_row24_traceSegment_045_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 882 9 9, g32p_row24_traceSegment_045_0882_0009, g32p_row24_traceSegment_045_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 864 18 18, g32p_row24_traceSegment_045_0864_0018, g32p_row24_traceSegment_045_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 900 9 9, g32p_row24_traceSegment_045_0900_0009, g32p_row24_traceSegment_045_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 927 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 918 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 918 9 9, g32p_row24_traceSegment_045_0918_0009, g32p_row24_traceSegment_045_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 900 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 900 18 18, g32p_row24_traceSegment_045_0900_0018, g32p_row24_traceSegment_045_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 864 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 864 36 36, g32p_row24_traceSegment_045_0864_0036, g32p_row24_traceSegment_045_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 936 9 9, g32p_row24_traceSegment_045_0936_0009, g32p_row24_traceSegment_045_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 954 9 9, g32p_row24_traceSegment_045_0954_0009, g32p_row24_traceSegment_045_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 936 18 18, g32p_row24_traceSegment_045_0936_0018, g32p_row24_traceSegment_045_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 972 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 972 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 972 9 9, g32p_row24_traceSegment_045_0972_0009, g32p_row24_traceSegment_045_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 990 9 9, g32p_row24_traceSegment_045_0990_0009, g32p_row24_traceSegment_045_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 972 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 972 18 18, g32p_row24_traceSegment_045_0972_0018, g32p_row24_traceSegment_045_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 936 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 936 36 36, g32p_row24_traceSegment_045_0936_0036, g32p_row24_traceSegment_045_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 864 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 864 72 72, g32p_row24_traceSegment_045_0864_0072, g32p_row24_traceSegment_045_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1008 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1017 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1008 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1008 9 9, g32p_row24_traceSegment_045_1008_0009, g32p_row24_traceSegment_045_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1026 9 9, g32p_row24_traceSegment_045_1026_0009, g32p_row24_traceSegment_045_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 1008 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1008 18 18, g32p_row24_traceSegment_045_1008_0018, g32p_row24_traceSegment_045_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1044 9 9, g32p_row24_traceSegment_045_1044_0009, g32p_row24_traceSegment_045_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1062 9 9, g32p_row24_traceSegment_045_1062_0009, g32p_row24_traceSegment_045_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1044 18 18, g32p_row24_traceSegment_045_1044_0018, g32p_row24_traceSegment_045_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 1008 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1008 36 36, g32p_row24_traceSegment_045_1008_0036, g32p_row24_traceSegment_045_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1080 9 9, g32p_row24_traceSegment_045_1080_0009, g32p_row24_traceSegment_045_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1098 9 9, g32p_row24_traceSegment_045_1098_0009, g32p_row24_traceSegment_045_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1080 18 18, g32p_row24_traceSegment_045_1080_0018, g32p_row24_traceSegment_045_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1116 9 9, g32p_row24_traceSegment_045_1116_0009, g32p_row24_traceSegment_045_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_045 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_045_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_045 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1134 9 9, g32p_row24_traceSegment_045_1134_0009, g32p_row24_traceSegment_045_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_045 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1116 18 18, g32p_row24_traceSegment_045_1116_0018, g32p_row24_traceSegment_045_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_045 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1080 36 36, g32p_row24_traceSegment_045_1080_0036, g32p_row24_traceSegment_045_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_045_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_045 1008 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 1008 72 72, g32p_row24_traceSegment_045_1008_0072, g32p_row24_traceSegment_045_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_045 864 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 864 144 144, g32p_row24_traceSegment_045_0864_0144, g32p_row24_traceSegment_045_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_045 576 576 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 576 288 288, g32p_row24_traceSegment_045_0576_0288, g32p_row24_traceSegment_045_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_045_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_045 0 1152 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_045 0 576 576, g32p_row24_traceSegment_045_0000_0576, g32p_row24_traceSegment_045_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 45 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_045_0000_1152

end HodgeLean.Foundations.Program

end
end
