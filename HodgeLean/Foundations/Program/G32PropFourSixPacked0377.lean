import HodgeLean.Foundations.Program.G32PropFourSixPacked0376
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_018_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 9 9, g32p_row19_traceSegment_018_0000_0009, g32p_row19_traceSegment_018_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 27 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 18 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 18 9 9, g32p_row19_traceSegment_018_0018_0009, g32p_row19_traceSegment_018_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 0 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 18 18, g32p_row19_traceSegment_018_0000_0018, g32p_row19_traceSegment_018_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 45 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 36 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 36 9 9, g32p_row19_traceSegment_018_0036_0009, g32p_row19_traceSegment_018_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 63 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 54 9 9, g32p_row19_traceSegment_018_0054_0009, g32p_row19_traceSegment_018_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 36 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 36 18 18, g32p_row19_traceSegment_018_0036_0018, g32p_row19_traceSegment_018_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 0 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 36 36, g32p_row19_traceSegment_018_0000_0036, g32p_row19_traceSegment_018_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 72 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 72 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 72 9 9, g32p_row19_traceSegment_018_0072_0009, g32p_row19_traceSegment_018_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 90 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 90 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 90 9 9, g32p_row19_traceSegment_018_0090_0009, g32p_row19_traceSegment_018_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 72 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 72 18 18, g32p_row19_traceSegment_018_0072_0018, g32p_row19_traceSegment_018_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 108 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 108 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 108 9 9, g32p_row19_traceSegment_018_0108_0009, g32p_row19_traceSegment_018_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 126 9 9, g32p_row19_traceSegment_018_0126_0009, g32p_row19_traceSegment_018_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 108 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 108 18 18, g32p_row19_traceSegment_018_0108_0018, g32p_row19_traceSegment_018_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 72 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 72 36 36, g32p_row19_traceSegment_018_0072_0036, g32p_row19_traceSegment_018_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 0 144 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 72 72, g32p_row19_traceSegment_018_0000_0072, g32p_row19_traceSegment_018_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 144 9 9, g32p_row19_traceSegment_018_0144_0009, g32p_row19_traceSegment_018_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 162 9 9, g32p_row19_traceSegment_018_0162_0009, g32p_row19_traceSegment_018_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 144 18 18, g32p_row19_traceSegment_018_0144_0018, g32p_row19_traceSegment_018_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 180 9 9, g32p_row19_traceSegment_018_0180_0009, g32p_row19_traceSegment_018_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 198 9 9, g32p_row19_traceSegment_018_0198_0009, g32p_row19_traceSegment_018_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 180 18 18, g32p_row19_traceSegment_018_0180_0018, g32p_row19_traceSegment_018_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 144 36 36, g32p_row19_traceSegment_018_0144_0036, g32p_row19_traceSegment_018_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 216 9 9, g32p_row19_traceSegment_018_0216_0009, g32p_row19_traceSegment_018_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 234 9 9, g32p_row19_traceSegment_018_0234_0009, g32p_row19_traceSegment_018_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 216 18 18, g32p_row19_traceSegment_018_0216_0018, g32p_row19_traceSegment_018_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 252 9 9, g32p_row19_traceSegment_018_0252_0009, g32p_row19_traceSegment_018_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 270 9 9, g32p_row19_traceSegment_018_0270_0009, g32p_row19_traceSegment_018_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 252 18 18, g32p_row19_traceSegment_018_0252_0018, g32p_row19_traceSegment_018_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 216 36 36, g32p_row19_traceSegment_018_0216_0036, g32p_row19_traceSegment_018_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 144 72 72, g32p_row19_traceSegment_018_0144_0072, g32p_row19_traceSegment_018_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_018 0 288 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 144 144, g32p_row19_traceSegment_018_0000_0144, g32p_row19_traceSegment_018_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 288 9 9, g32p_row19_traceSegment_018_0288_0009, g32p_row19_traceSegment_018_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 306 9 9, g32p_row19_traceSegment_018_0306_0009, g32p_row19_traceSegment_018_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 288 18 18, g32p_row19_traceSegment_018_0288_0018, g32p_row19_traceSegment_018_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 324 9 9, g32p_row19_traceSegment_018_0324_0009, g32p_row19_traceSegment_018_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 342 9 9, g32p_row19_traceSegment_018_0342_0009, g32p_row19_traceSegment_018_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 324 18 18, g32p_row19_traceSegment_018_0324_0018, g32p_row19_traceSegment_018_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 288 36 36, g32p_row19_traceSegment_018_0288_0036, g32p_row19_traceSegment_018_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 360 9 9, g32p_row19_traceSegment_018_0360_0009, g32p_row19_traceSegment_018_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 378 9 9, g32p_row19_traceSegment_018_0378_0009, g32p_row19_traceSegment_018_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 360 18 18, g32p_row19_traceSegment_018_0360_0018, g32p_row19_traceSegment_018_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 396 9 9, g32p_row19_traceSegment_018_0396_0009, g32p_row19_traceSegment_018_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 414 9 9, g32p_row19_traceSegment_018_0414_0009, g32p_row19_traceSegment_018_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 396 18 18, g32p_row19_traceSegment_018_0396_0018, g32p_row19_traceSegment_018_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 360 36 36, g32p_row19_traceSegment_018_0360_0036, g32p_row19_traceSegment_018_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 288 72 72, g32p_row19_traceSegment_018_0288_0072, g32p_row19_traceSegment_018_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 432 9 9, g32p_row19_traceSegment_018_0432_0009, g32p_row19_traceSegment_018_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 450 9 9, g32p_row19_traceSegment_018_0450_0009, g32p_row19_traceSegment_018_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 432 18 18, g32p_row19_traceSegment_018_0432_0018, g32p_row19_traceSegment_018_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 468 9 9, g32p_row19_traceSegment_018_0468_0009, g32p_row19_traceSegment_018_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 486 9 9, g32p_row19_traceSegment_018_0486_0009, g32p_row19_traceSegment_018_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 468 18 18, g32p_row19_traceSegment_018_0468_0018, g32p_row19_traceSegment_018_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 432 36 36, g32p_row19_traceSegment_018_0432_0036, g32p_row19_traceSegment_018_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 504 9 9, g32p_row19_traceSegment_018_0504_0009, g32p_row19_traceSegment_018_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 522 9 9, g32p_row19_traceSegment_018_0522_0009, g32p_row19_traceSegment_018_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 504 18 18, g32p_row19_traceSegment_018_0504_0018, g32p_row19_traceSegment_018_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 540 9 9, g32p_row19_traceSegment_018_0540_0009, g32p_row19_traceSegment_018_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 558 9 9, g32p_row19_traceSegment_018_0558_0009, g32p_row19_traceSegment_018_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 540 18 18, g32p_row19_traceSegment_018_0540_0018, g32p_row19_traceSegment_018_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 504 36 36, g32p_row19_traceSegment_018_0504_0036, g32p_row19_traceSegment_018_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 432 72 72, g32p_row19_traceSegment_018_0432_0072, g32p_row19_traceSegment_018_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_018 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 288 144 144, g32p_row19_traceSegment_018_0288_0144, g32p_row19_traceSegment_018_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_018 0 576 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 288 288, g32p_row19_traceSegment_018_0000_0288, g32p_row19_traceSegment_018_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 576 9 9, g32p_row19_traceSegment_018_0576_0009, g32p_row19_traceSegment_018_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 594 9 9, g32p_row19_traceSegment_018_0594_0009, g32p_row19_traceSegment_018_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 576 18 18, g32p_row19_traceSegment_018_0576_0018, g32p_row19_traceSegment_018_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 621 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 612 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 612 9 9, g32p_row19_traceSegment_018_0612_0009, g32p_row19_traceSegment_018_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 630 9 9, g32p_row19_traceSegment_018_0630_0009, g32p_row19_traceSegment_018_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 612 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 612 18 18, g32p_row19_traceSegment_018_0612_0018, g32p_row19_traceSegment_018_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 576 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 576 36 36, g32p_row19_traceSegment_018_0576_0036, g32p_row19_traceSegment_018_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 648 9 9, g32p_row19_traceSegment_018_0648_0009, g32p_row19_traceSegment_018_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 666 9 9, g32p_row19_traceSegment_018_0666_0009, g32p_row19_traceSegment_018_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 648 18 18, g32p_row19_traceSegment_018_0648_0018, g32p_row19_traceSegment_018_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 684 9 9, g32p_row19_traceSegment_018_0684_0009, g32p_row19_traceSegment_018_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 711 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 702 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 702 9 9, g32p_row19_traceSegment_018_0702_0009, g32p_row19_traceSegment_018_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 684 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 684 18 18, g32p_row19_traceSegment_018_0684_0018, g32p_row19_traceSegment_018_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 648 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 648 36 36, g32p_row19_traceSegment_018_0648_0036, g32p_row19_traceSegment_018_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 576 144 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 576 72 72, g32p_row19_traceSegment_018_0576_0072, g32p_row19_traceSegment_018_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 720 9 9, g32p_row19_traceSegment_018_0720_0009, g32p_row19_traceSegment_018_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 738 9 9, g32p_row19_traceSegment_018_0738_0009, g32p_row19_traceSegment_018_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 720 18 18, g32p_row19_traceSegment_018_0720_0018, g32p_row19_traceSegment_018_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 756 9 9, g32p_row19_traceSegment_018_0756_0009, g32p_row19_traceSegment_018_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 774 9 9, g32p_row19_traceSegment_018_0774_0009, g32p_row19_traceSegment_018_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 756 18 18, g32p_row19_traceSegment_018_0756_0018, g32p_row19_traceSegment_018_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 720 36 36, g32p_row19_traceSegment_018_0720_0036, g32p_row19_traceSegment_018_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 792 9 9, g32p_row19_traceSegment_018_0792_0009, g32p_row19_traceSegment_018_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 819 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 810 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 810 9 9, g32p_row19_traceSegment_018_0810_0009, g32p_row19_traceSegment_018_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 792 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 792 18 18, g32p_row19_traceSegment_018_0792_0018, g32p_row19_traceSegment_018_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 828 9 9, g32p_row19_traceSegment_018_0828_0009, g32p_row19_traceSegment_018_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 846 9 9, g32p_row19_traceSegment_018_0846_0009, g32p_row19_traceSegment_018_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 828 18 18, g32p_row19_traceSegment_018_0828_0018, g32p_row19_traceSegment_018_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 792 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 792 36 36, g32p_row19_traceSegment_018_0792_0036, g32p_row19_traceSegment_018_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 720 144 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 720 72 72, g32p_row19_traceSegment_018_0720_0072, g32p_row19_traceSegment_018_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_018 576 288 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 576 144 144, g32p_row19_traceSegment_018_0576_0144, g32p_row19_traceSegment_018_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 864 9 9, g32p_row19_traceSegment_018_0864_0009, g32p_row19_traceSegment_018_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 882 9 9, g32p_row19_traceSegment_018_0882_0009, g32p_row19_traceSegment_018_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 864 18 18, g32p_row19_traceSegment_018_0864_0018, g32p_row19_traceSegment_018_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 900 9 9, g32p_row19_traceSegment_018_0900_0009, g32p_row19_traceSegment_018_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 918 9 9, g32p_row19_traceSegment_018_0918_0009, g32p_row19_traceSegment_018_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 900 18 18, g32p_row19_traceSegment_018_0900_0018, g32p_row19_traceSegment_018_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 864 36 36, g32p_row19_traceSegment_018_0864_0036, g32p_row19_traceSegment_018_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 936 9 9, g32p_row19_traceSegment_018_0936_0009, g32p_row19_traceSegment_018_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 954 9 9, g32p_row19_traceSegment_018_0954_0009, g32p_row19_traceSegment_018_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 936 18 18, g32p_row19_traceSegment_018_0936_0018, g32p_row19_traceSegment_018_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 972 9 9, g32p_row19_traceSegment_018_0972_0009, g32p_row19_traceSegment_018_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 990 9 9, g32p_row19_traceSegment_018_0990_0009, g32p_row19_traceSegment_018_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 972 18 18, g32p_row19_traceSegment_018_0972_0018, g32p_row19_traceSegment_018_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 936 36 36, g32p_row19_traceSegment_018_0936_0036, g32p_row19_traceSegment_018_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 864 72 72, g32p_row19_traceSegment_018_0864_0072, g32p_row19_traceSegment_018_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1008 9 9, g32p_row19_traceSegment_018_1008_0009, g32p_row19_traceSegment_018_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1026 9 9, g32p_row19_traceSegment_018_1026_0009, g32p_row19_traceSegment_018_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1008 18 18, g32p_row19_traceSegment_018_1008_0018, g32p_row19_traceSegment_018_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1044 9 9, g32p_row19_traceSegment_018_1044_0009, g32p_row19_traceSegment_018_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1062 9 9, g32p_row19_traceSegment_018_1062_0009, g32p_row19_traceSegment_018_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1044 18 18, g32p_row19_traceSegment_018_1044_0018, g32p_row19_traceSegment_018_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1008 36 36, g32p_row19_traceSegment_018_1008_0036, g32p_row19_traceSegment_018_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1080 9 9, g32p_row19_traceSegment_018_1080_0009, g32p_row19_traceSegment_018_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1098 9 9, g32p_row19_traceSegment_018_1098_0009, g32p_row19_traceSegment_018_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1080 18 18, g32p_row19_traceSegment_018_1080_0018, g32p_row19_traceSegment_018_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1116 9 9, g32p_row19_traceSegment_018_1116_0009, g32p_row19_traceSegment_018_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_018 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_018_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_018 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1134 9 9, g32p_row19_traceSegment_018_1134_0009, g32p_row19_traceSegment_018_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_018 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1116 18 18, g32p_row19_traceSegment_018_1116_0018, g32p_row19_traceSegment_018_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_018 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1080 36 36, g32p_row19_traceSegment_018_1080_0036, g32p_row19_traceSegment_018_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_018_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_018 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 1008 72 72, g32p_row19_traceSegment_018_1008_0072, g32p_row19_traceSegment_018_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_018 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 864 144 144, g32p_row19_traceSegment_018_0864_0144, g32p_row19_traceSegment_018_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_018 576 576 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 576 288 288, g32p_row19_traceSegment_018_0576_0288, g32p_row19_traceSegment_018_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_018_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_018 0 1152 = [2, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_018 0 576 576, g32p_row19_traceSegment_018_0000_0576, g32p_row19_traceSegment_018_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 18 = [2, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_018_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_021 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 21 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_021_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 9 9, g32p_row19_traceSegment_021_0000_0009, g32p_row19_traceSegment_021_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 18 9 9, g32p_row19_traceSegment_021_0018_0009, g32p_row19_traceSegment_021_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 18 18, g32p_row19_traceSegment_021_0000_0018, g32p_row19_traceSegment_021_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 36 9 9, g32p_row19_traceSegment_021_0036_0009, g32p_row19_traceSegment_021_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 54 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 54 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 54 9 9, g32p_row19_traceSegment_021_0054_0009, g32p_row19_traceSegment_021_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 36 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 36 18 18, g32p_row19_traceSegment_021_0036_0018, g32p_row19_traceSegment_021_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 0 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 36 36, g32p_row19_traceSegment_021_0000_0036, g32p_row19_traceSegment_021_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 72 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 81 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 72 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 72 9 9, g32p_row19_traceSegment_021_0072_0009, g32p_row19_traceSegment_021_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 90 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 90 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 90 9 9, g32p_row19_traceSegment_021_0090_0009, g32p_row19_traceSegment_021_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 72 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 72 18 18, g32p_row19_traceSegment_021_0072_0018, g32p_row19_traceSegment_021_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 108 9 9, g32p_row19_traceSegment_021_0108_0009, g32p_row19_traceSegment_021_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 126 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 126 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 126 9 9, g32p_row19_traceSegment_021_0126_0009, g32p_row19_traceSegment_021_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 108 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 108 18 18, g32p_row19_traceSegment_021_0108_0018, g32p_row19_traceSegment_021_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 72 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 72 36 36, g32p_row19_traceSegment_021_0072_0036, g32p_row19_traceSegment_021_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 0 144 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 72 72, g32p_row19_traceSegment_021_0000_0072, g32p_row19_traceSegment_021_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 153 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 144 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 144 9 9, g32p_row19_traceSegment_021_0144_0009, g32p_row19_traceSegment_021_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 171 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 162 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 162 9 9, g32p_row19_traceSegment_021_0162_0009, g32p_row19_traceSegment_021_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 144 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 144 18 18, g32p_row19_traceSegment_021_0144_0018, g32p_row19_traceSegment_021_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 180 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 189 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 180 18 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 180 9 9, g32p_row19_traceSegment_021_0180_0009, g32p_row19_traceSegment_021_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 198 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 207 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 198 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 198 9 9, g32p_row19_traceSegment_021_0198_0009, g32p_row19_traceSegment_021_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 180 36 = [0, 2, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 180 18 18, g32p_row19_traceSegment_021_0180_0018, g32p_row19_traceSegment_021_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 144 72 = [0, 5, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 144 36 36, g32p_row19_traceSegment_021_0144_0036, g32p_row19_traceSegment_021_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 216 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 216 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 216 9 9, g32p_row19_traceSegment_021_0216_0009, g32p_row19_traceSegment_021_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 234 9 9, g32p_row19_traceSegment_021_0234_0009, g32p_row19_traceSegment_021_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 216 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 216 18 18, g32p_row19_traceSegment_021_0216_0018, g32p_row19_traceSegment_021_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 252 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 252 9 9, g32p_row19_traceSegment_021_0252_0009, g32p_row19_traceSegment_021_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 270 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 270 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 270 9 9, g32p_row19_traceSegment_021_0270_0009, g32p_row19_traceSegment_021_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 252 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 252 18 18, g32p_row19_traceSegment_021_0252_0018, g32p_row19_traceSegment_021_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 216 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 216 36 36, g32p_row19_traceSegment_021_0216_0036, g32p_row19_traceSegment_021_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 144 144 = [0, 5, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 144 72 72, g32p_row19_traceSegment_021_0144_0072, g32p_row19_traceSegment_021_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_021 0 288 = [0, 12, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 144 144, g32p_row19_traceSegment_021_0000_0144, g32p_row19_traceSegment_021_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 288 9 9, g32p_row19_traceSegment_021_0288_0009, g32p_row19_traceSegment_021_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 306 9 9, g32p_row19_traceSegment_021_0306_0009, g32p_row19_traceSegment_021_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 288 18 18, g32p_row19_traceSegment_021_0288_0018, g32p_row19_traceSegment_021_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 324 9 9, g32p_row19_traceSegment_021_0324_0009, g32p_row19_traceSegment_021_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 351 9 = [0, 1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 342 18 = [0, 1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 342 9 9, g32p_row19_traceSegment_021_0342_0009, g32p_row19_traceSegment_021_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 324 36 = [0, 1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 324 18 18, g32p_row19_traceSegment_021_0324_0018, g32p_row19_traceSegment_021_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 288 72 = [0, 1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 288 36 36, g32p_row19_traceSegment_021_0288_0036, g32p_row19_traceSegment_021_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 360 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 369 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 360 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 360 9 9, g32p_row19_traceSegment_021_0360_0009, g32p_row19_traceSegment_021_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 378 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 387 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 378 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 378 9 9, g32p_row19_traceSegment_021_0378_0009, g32p_row19_traceSegment_021_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 360 36 = [0, 2, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 360 18 18, g32p_row19_traceSegment_021_0360_0018, g32p_row19_traceSegment_021_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 396 9 = [0, 1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 405 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 396 18 = [0, 1, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 396 9 9, g32p_row19_traceSegment_021_0396_0009, g32p_row19_traceSegment_021_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 423 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 414 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 414 9 9, g32p_row19_traceSegment_021_0414_0009, g32p_row19_traceSegment_021_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 396 36 = [0, 1, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 396 18 18, g32p_row19_traceSegment_021_0396_0018, g32p_row19_traceSegment_021_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 360 72 = [0, 3, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 360 36 36, g32p_row19_traceSegment_021_0360_0036, g32p_row19_traceSegment_021_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 288 144 = [0, 4, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 288 72 72, g32p_row19_traceSegment_021_0288_0072, g32p_row19_traceSegment_021_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 432 9 9, g32p_row19_traceSegment_021_0432_0009, g32p_row19_traceSegment_021_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 450 9 9, g32p_row19_traceSegment_021_0450_0009, g32p_row19_traceSegment_021_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 432 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 432 18 18, g32p_row19_traceSegment_021_0432_0018, g32p_row19_traceSegment_021_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 468 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 477 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 468 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 468 9 9, g32p_row19_traceSegment_021_0468_0009, g32p_row19_traceSegment_021_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 495 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 486 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 486 9 9, g32p_row19_traceSegment_021_0486_0009, g32p_row19_traceSegment_021_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 468 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 468 18 18, g32p_row19_traceSegment_021_0468_0018, g32p_row19_traceSegment_021_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 432 72 = [0, 1, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 432 36 36, g32p_row19_traceSegment_021_0432_0036, g32p_row19_traceSegment_021_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 504 9 9, g32p_row19_traceSegment_021_0504_0009, g32p_row19_traceSegment_021_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 522 9 9, g32p_row19_traceSegment_021_0522_0009, g32p_row19_traceSegment_021_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 504 18 18, g32p_row19_traceSegment_021_0504_0018, g32p_row19_traceSegment_021_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 549 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 540 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 540 9 9, g32p_row19_traceSegment_021_0540_0009, g32p_row19_traceSegment_021_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 567 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 558 9 9, g32p_row19_traceSegment_021_0558_0009, g32p_row19_traceSegment_021_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 540 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 540 18 18, g32p_row19_traceSegment_021_0540_0018, g32p_row19_traceSegment_021_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 504 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 504 36 36, g32p_row19_traceSegment_021_0504_0036, g32p_row19_traceSegment_021_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 432 144 = [0, 3, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 432 72 72, g32p_row19_traceSegment_021_0432_0072, g32p_row19_traceSegment_021_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_021 288 288 = [0, 7, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 288 144 144, g32p_row19_traceSegment_021_0288_0144, g32p_row19_traceSegment_021_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_021 0 576 = [0, 19, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 288 288, g32p_row19_traceSegment_021_0000_0288, g32p_row19_traceSegment_021_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 576 9 9, g32p_row19_traceSegment_021_0576_0009, g32p_row19_traceSegment_021_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 603 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 594 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 594 9 9, g32p_row19_traceSegment_021_0594_0009, g32p_row19_traceSegment_021_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 576 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 576 18 18, g32p_row19_traceSegment_021_0576_0018, g32p_row19_traceSegment_021_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 612 9 9, g32p_row19_traceSegment_021_0612_0009, g32p_row19_traceSegment_021_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 630 9 9, g32p_row19_traceSegment_021_0630_0009, g32p_row19_traceSegment_021_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 612 18 18, g32p_row19_traceSegment_021_0612_0018, g32p_row19_traceSegment_021_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 576 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 576 36 36, g32p_row19_traceSegment_021_0576_0036, g32p_row19_traceSegment_021_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 648 9 = [0, 1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 657 9 = [0, 1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 648 18 = [0, 2, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 648 9 9, g32p_row19_traceSegment_021_0648_0009, g32p_row19_traceSegment_021_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 675 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 666 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 666 9 9, g32p_row19_traceSegment_021_0666_0009, g32p_row19_traceSegment_021_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 648 36 = [0, 2, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 648 18 18, g32p_row19_traceSegment_021_0648_0018, g32p_row19_traceSegment_021_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 684 9 = [0, 2, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 684 18 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 684 9 9, g32p_row19_traceSegment_021_0684_0009, g32p_row19_traceSegment_021_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 702 9 9, g32p_row19_traceSegment_021_0702_0009, g32p_row19_traceSegment_021_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 684 36 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 684 18 18, g32p_row19_traceSegment_021_0684_0018, g32p_row19_traceSegment_021_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 648 72 = [0, 4, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 648 36 36, g32p_row19_traceSegment_021_0648_0036, g32p_row19_traceSegment_021_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 576 144 = [0, 4, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 576 72 72, g32p_row19_traceSegment_021_0576_0072, g32p_row19_traceSegment_021_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 729 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 720 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 720 9 9, g32p_row19_traceSegment_021_0720_0009, g32p_row19_traceSegment_021_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 747 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 738 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 738 9 9, g32p_row19_traceSegment_021_0738_0009, g32p_row19_traceSegment_021_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 720 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 720 18 18, g32p_row19_traceSegment_021_0720_0018, g32p_row19_traceSegment_021_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 756 9 = [0, 2, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 756 18 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 756 9 9, g32p_row19_traceSegment_021_0756_0009, g32p_row19_traceSegment_021_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 774 9 9, g32p_row19_traceSegment_021_0774_0009, g32p_row19_traceSegment_021_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 756 36 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 756 18 18, g32p_row19_traceSegment_021_0756_0018, g32p_row19_traceSegment_021_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 720 72 = [0, 2, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 720 36 36, g32p_row19_traceSegment_021_0720_0036, g32p_row19_traceSegment_021_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 792 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 801 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 792 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 792 9 9, g32p_row19_traceSegment_021_0792_0009, g32p_row19_traceSegment_021_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 810 9 9, g32p_row19_traceSegment_021_0810_0009, g32p_row19_traceSegment_021_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 792 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 792 18 18, g32p_row19_traceSegment_021_0792_0018, g32p_row19_traceSegment_021_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 828 9 9, g32p_row19_traceSegment_021_0828_0009, g32p_row19_traceSegment_021_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 846 9 9, g32p_row19_traceSegment_021_0846_0009, g32p_row19_traceSegment_021_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 828 18 18, g32p_row19_traceSegment_021_0828_0018, g32p_row19_traceSegment_021_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 792 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 792 36 36, g32p_row19_traceSegment_021_0792_0036, g32p_row19_traceSegment_021_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 720 144 = [0, 4, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 720 72 72, g32p_row19_traceSegment_021_0720_0072, g32p_row19_traceSegment_021_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_021 576 288 = [0, 8, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 576 144 144, g32p_row19_traceSegment_021_0576_0144, g32p_row19_traceSegment_021_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 864 9 9, g32p_row19_traceSegment_021_0864_0009, g32p_row19_traceSegment_021_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 891 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 882 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 882 9 9, g32p_row19_traceSegment_021_0882_0009, g32p_row19_traceSegment_021_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 864 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 864 18 18, g32p_row19_traceSegment_021_0864_0018, g32p_row19_traceSegment_021_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 900 9 9, g32p_row19_traceSegment_021_0900_0009, g32p_row19_traceSegment_021_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 918 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 918 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 918 9 9, g32p_row19_traceSegment_021_0918_0009, g32p_row19_traceSegment_021_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 900 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 900 18 18, g32p_row19_traceSegment_021_0900_0018, g32p_row19_traceSegment_021_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 864 72 = [0, 1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 864 36 36, g32p_row19_traceSegment_021_0864_0036, g32p_row19_traceSegment_021_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 936 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 945 9 = [0, 1, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 936 18 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 936 9 9, g32p_row19_traceSegment_021_0936_0009, g32p_row19_traceSegment_021_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 954 9 9, g32p_row19_traceSegment_021_0954_0009, g32p_row19_traceSegment_021_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 936 36 = [0, 2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 936 18 18, g32p_row19_traceSegment_021_0936_0018, g32p_row19_traceSegment_021_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 972 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 981 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 972 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 972 9 9, g32p_row19_traceSegment_021_0972_0009, g32p_row19_traceSegment_021_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 999 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 990 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 990 9 9, g32p_row19_traceSegment_021_0990_0009, g32p_row19_traceSegment_021_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 972 36 = [0, 1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 972 18 18, g32p_row19_traceSegment_021_0972_0018, g32p_row19_traceSegment_021_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 936 72 = [0, 3, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 936 36 36, g32p_row19_traceSegment_021_0936_0036, g32p_row19_traceSegment_021_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 864 144 = [0, 4, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 864 72 72, g32p_row19_traceSegment_021_0864_0072, g32p_row19_traceSegment_021_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1008 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1008 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1008 9 9, g32p_row19_traceSegment_021_1008_0009, g32p_row19_traceSegment_021_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1026 9 9, g32p_row19_traceSegment_021_1026_0009, g32p_row19_traceSegment_021_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 1008 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1008 18 18, g32p_row19_traceSegment_021_1008_0018, g32p_row19_traceSegment_021_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1044 9 9, g32p_row19_traceSegment_021_1044_0009, g32p_row19_traceSegment_021_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1062 9 9, g32p_row19_traceSegment_021_1062_0009, g32p_row19_traceSegment_021_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1044 18 18, g32p_row19_traceSegment_021_1044_0018, g32p_row19_traceSegment_021_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 1008 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1008 36 36, g32p_row19_traceSegment_021_1008_0036, g32p_row19_traceSegment_021_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1080 9 9, g32p_row19_traceSegment_021_1080_0009, g32p_row19_traceSegment_021_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1098 9 9, g32p_row19_traceSegment_021_1098_0009, g32p_row19_traceSegment_021_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1080 18 18, g32p_row19_traceSegment_021_1080_0018, g32p_row19_traceSegment_021_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1116 9 9, g32p_row19_traceSegment_021_1116_0009, g32p_row19_traceSegment_021_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_021 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_021_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_021 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1134 9 9, g32p_row19_traceSegment_021_1134_0009, g32p_row19_traceSegment_021_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_021 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1116 18 18, g32p_row19_traceSegment_021_1116_0018, g32p_row19_traceSegment_021_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_021 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1080 36 36, g32p_row19_traceSegment_021_1080_0036, g32p_row19_traceSegment_021_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_021_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_021 1008 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 1008 72 72, g32p_row19_traceSegment_021_1008_0072, g32p_row19_traceSegment_021_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_021 864 288 = [0, 5, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 864 144 144, g32p_row19_traceSegment_021_0864_0144, g32p_row19_traceSegment_021_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_021 576 576 = [0, 13, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 576 288 288, g32p_row19_traceSegment_021_0576_0288, g32p_row19_traceSegment_021_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_021_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_021 0 1152 = [0, 32, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_021 0 576 576, g32p_row19_traceSegment_021_0000_0576, g32p_row19_traceSegment_021_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_021 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 21 = [0, 32, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_021_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_024_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 9 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 9 9, g32p_row19_traceSegment_024_0000_0009, g32p_row19_traceSegment_024_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 18 9 9, g32p_row19_traceSegment_024_0018_0009, g32p_row19_traceSegment_024_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 18 18, g32p_row19_traceSegment_024_0000_0018, g32p_row19_traceSegment_024_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 36 9 = [0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 45 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 36 18 = [0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 36 9 9, g32p_row19_traceSegment_024_0036_0009, g32p_row19_traceSegment_024_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 54 9 9, g32p_row19_traceSegment_024_0054_0009, g32p_row19_traceSegment_024_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 36 36 = [0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 36 18 18, g32p_row19_traceSegment_024_0036_0018, g32p_row19_traceSegment_024_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 0 72 = [0, 0, 3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 36 36, g32p_row19_traceSegment_024_0000_0036, g32p_row19_traceSegment_024_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 72 9 9, g32p_row19_traceSegment_024_0072_0009, g32p_row19_traceSegment_024_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 90 9 9, g32p_row19_traceSegment_024_0090_0009, g32p_row19_traceSegment_024_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 72 18 18, g32p_row19_traceSegment_024_0072_0018, g32p_row19_traceSegment_024_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 108 9 9, g32p_row19_traceSegment_024_0108_0009, g32p_row19_traceSegment_024_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 126 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 126 9 9, g32p_row19_traceSegment_024_0126_0009, g32p_row19_traceSegment_024_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 108 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 108 18 18, g32p_row19_traceSegment_024_0108_0018, g32p_row19_traceSegment_024_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 72 36 36, g32p_row19_traceSegment_024_0072_0036, g32p_row19_traceSegment_024_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 0 144 = [0, 0, 5, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 72 72, g32p_row19_traceSegment_024_0000_0072, g32p_row19_traceSegment_024_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 144 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 144 9 9, g32p_row19_traceSegment_024_0144_0009, g32p_row19_traceSegment_024_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 162 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 162 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 162 9 9, g32p_row19_traceSegment_024_0162_0009, g32p_row19_traceSegment_024_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 144 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 144 18 18, g32p_row19_traceSegment_024_0144_0018, g32p_row19_traceSegment_024_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 180 9 9, g32p_row19_traceSegment_024_0180_0009, g32p_row19_traceSegment_024_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 198 9 9, g32p_row19_traceSegment_024_0198_0009, g32p_row19_traceSegment_024_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 180 18 18, g32p_row19_traceSegment_024_0180_0018, g32p_row19_traceSegment_024_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 144 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 144 36 36, g32p_row19_traceSegment_024_0144_0036, g32p_row19_traceSegment_024_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 216 9 9, g32p_row19_traceSegment_024_0216_0009, g32p_row19_traceSegment_024_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 234 9 9, g32p_row19_traceSegment_024_0234_0009, g32p_row19_traceSegment_024_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 216 18 18, g32p_row19_traceSegment_024_0216_0018, g32p_row19_traceSegment_024_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 252 9 9, g32p_row19_traceSegment_024_0252_0009, g32p_row19_traceSegment_024_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 270 9 9, g32p_row19_traceSegment_024_0270_0009, g32p_row19_traceSegment_024_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 252 18 18, g32p_row19_traceSegment_024_0252_0018, g32p_row19_traceSegment_024_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 216 36 36, g32p_row19_traceSegment_024_0216_0036, g32p_row19_traceSegment_024_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 144 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 144 72 72, g32p_row19_traceSegment_024_0144_0072, g32p_row19_traceSegment_024_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_024 0 288 = [0, 0, 7, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 144 144, g32p_row19_traceSegment_024_0000_0144, g32p_row19_traceSegment_024_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 288 9 9, g32p_row19_traceSegment_024_0288_0009, g32p_row19_traceSegment_024_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 306 9 9, g32p_row19_traceSegment_024_0306_0009, g32p_row19_traceSegment_024_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 288 18 18, g32p_row19_traceSegment_024_0288_0018, g32p_row19_traceSegment_024_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 324 9 9, g32p_row19_traceSegment_024_0324_0009, g32p_row19_traceSegment_024_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 342 9 9, g32p_row19_traceSegment_024_0342_0009, g32p_row19_traceSegment_024_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 324 18 18, g32p_row19_traceSegment_024_0324_0018, g32p_row19_traceSegment_024_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 288 36 36, g32p_row19_traceSegment_024_0288_0036, g32p_row19_traceSegment_024_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 360 9 9, g32p_row19_traceSegment_024_0360_0009, g32p_row19_traceSegment_024_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 387 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 378 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 378 9 9, g32p_row19_traceSegment_024_0378_0009, g32p_row19_traceSegment_024_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 360 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 360 18 18, g32p_row19_traceSegment_024_0360_0018, g32p_row19_traceSegment_024_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 396 9 9, g32p_row19_traceSegment_024_0396_0009, g32p_row19_traceSegment_024_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 414 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 414 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 414 9 9, g32p_row19_traceSegment_024_0414_0009, g32p_row19_traceSegment_024_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 396 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 396 18 18, g32p_row19_traceSegment_024_0396_0018, g32p_row19_traceSegment_024_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 360 72 = [0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 360 36 36, g32p_row19_traceSegment_024_0360_0036, g32p_row19_traceSegment_024_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 288 144 = [0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 288 72 72, g32p_row19_traceSegment_024_0288_0072, g32p_row19_traceSegment_024_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 432 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 441 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 432 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 432 9 9, g32p_row19_traceSegment_024_0432_0009, g32p_row19_traceSegment_024_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 450 9 9, g32p_row19_traceSegment_024_0450_0009, g32p_row19_traceSegment_024_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 432 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 432 18 18, g32p_row19_traceSegment_024_0432_0018, g32p_row19_traceSegment_024_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 468 9 9, g32p_row19_traceSegment_024_0468_0009, g32p_row19_traceSegment_024_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 486 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 495 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 486 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 486 9 9, g32p_row19_traceSegment_024_0486_0009, g32p_row19_traceSegment_024_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 468 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 468 18 18, g32p_row19_traceSegment_024_0468_0018, g32p_row19_traceSegment_024_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 432 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 432 36 36, g32p_row19_traceSegment_024_0432_0036, g32p_row19_traceSegment_024_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 504 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 513 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 504 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 504 9 9, g32p_row19_traceSegment_024_0504_0009, g32p_row19_traceSegment_024_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 522 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 531 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 522 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 522 9 9, g32p_row19_traceSegment_024_0522_0009, g32p_row19_traceSegment_024_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 504 36 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 504 18 18, g32p_row19_traceSegment_024_0504_0018, g32p_row19_traceSegment_024_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 540 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 540 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 540 9 9, g32p_row19_traceSegment_024_0540_0009, g32p_row19_traceSegment_024_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 558 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 558 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 558 9 9, g32p_row19_traceSegment_024_0558_0009, g32p_row19_traceSegment_024_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 540 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 540 18 18, g32p_row19_traceSegment_024_0540_0018, g32p_row19_traceSegment_024_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 504 72 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 504 36 36, g32p_row19_traceSegment_024_0504_0036, g32p_row19_traceSegment_024_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 432 144 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 432 72 72, g32p_row19_traceSegment_024_0432_0072, g32p_row19_traceSegment_024_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_024 288 288 = [0, 0, 1, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 288 144 144, g32p_row19_traceSegment_024_0288_0144, g32p_row19_traceSegment_024_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_024 0 576 = [0, 0, 8, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 288 288, g32p_row19_traceSegment_024_0000_0288, g32p_row19_traceSegment_024_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 576 9 9, g32p_row19_traceSegment_024_0576_0009, g32p_row19_traceSegment_024_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 594 9 9, g32p_row19_traceSegment_024_0594_0009, g32p_row19_traceSegment_024_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 576 18 18, g32p_row19_traceSegment_024_0576_0018, g32p_row19_traceSegment_024_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 612 9 9, g32p_row19_traceSegment_024_0612_0009, g32p_row19_traceSegment_024_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 630 9 9, g32p_row19_traceSegment_024_0630_0009, g32p_row19_traceSegment_024_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 612 18 18, g32p_row19_traceSegment_024_0612_0018, g32p_row19_traceSegment_024_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 576 36 36, g32p_row19_traceSegment_024_0576_0036, g32p_row19_traceSegment_024_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 648 9 9, g32p_row19_traceSegment_024_0648_0009, g32p_row19_traceSegment_024_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 666 9 9, g32p_row19_traceSegment_024_0666_0009, g32p_row19_traceSegment_024_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 648 18 18, g32p_row19_traceSegment_024_0648_0018, g32p_row19_traceSegment_024_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 684 9 9, g32p_row19_traceSegment_024_0684_0009, g32p_row19_traceSegment_024_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 702 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 702 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 702 9 9, g32p_row19_traceSegment_024_0702_0009, g32p_row19_traceSegment_024_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 684 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 684 18 18, g32p_row19_traceSegment_024_0684_0018, g32p_row19_traceSegment_024_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 648 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 648 36 36, g32p_row19_traceSegment_024_0648_0036, g32p_row19_traceSegment_024_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 576 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 576 72 72, g32p_row19_traceSegment_024_0576_0072, g32p_row19_traceSegment_024_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 720 9 9, g32p_row19_traceSegment_024_0720_0009, g32p_row19_traceSegment_024_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 738 9 9, g32p_row19_traceSegment_024_0738_0009, g32p_row19_traceSegment_024_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 720 18 18, g32p_row19_traceSegment_024_0720_0018, g32p_row19_traceSegment_024_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 765 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 756 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 756 9 9, g32p_row19_traceSegment_024_0756_0009, g32p_row19_traceSegment_024_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 774 9 9, g32p_row19_traceSegment_024_0774_0009, g32p_row19_traceSegment_024_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 756 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 756 18 18, g32p_row19_traceSegment_024_0756_0018, g32p_row19_traceSegment_024_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 720 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 720 36 36, g32p_row19_traceSegment_024_0720_0036, g32p_row19_traceSegment_024_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 801 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 792 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 792 9 9, g32p_row19_traceSegment_024_0792_0009, g32p_row19_traceSegment_024_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 810 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 810 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 810 9 9, g32p_row19_traceSegment_024_0810_0009, g32p_row19_traceSegment_024_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 792 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 792 18 18, g32p_row19_traceSegment_024_0792_0018, g32p_row19_traceSegment_024_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 828 9 9, g32p_row19_traceSegment_024_0828_0009, g32p_row19_traceSegment_024_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 846 9 9, g32p_row19_traceSegment_024_0846_0009, g32p_row19_traceSegment_024_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 828 18 18, g32p_row19_traceSegment_024_0828_0018, g32p_row19_traceSegment_024_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 792 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 792 36 36, g32p_row19_traceSegment_024_0792_0036, g32p_row19_traceSegment_024_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 720 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 720 72 72, g32p_row19_traceSegment_024_0720_0072, g32p_row19_traceSegment_024_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_024 576 288 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 576 144 144, g32p_row19_traceSegment_024_0576_0144, g32p_row19_traceSegment_024_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 864 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 864 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 864 9 9, g32p_row19_traceSegment_024_0864_0009, g32p_row19_traceSegment_024_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 882 9 9, g32p_row19_traceSegment_024_0882_0009, g32p_row19_traceSegment_024_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 864 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 864 18 18, g32p_row19_traceSegment_024_0864_0018, g32p_row19_traceSegment_024_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 900 9 9, g32p_row19_traceSegment_024_0900_0009, g32p_row19_traceSegment_024_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 918 9 9, g32p_row19_traceSegment_024_0918_0009, g32p_row19_traceSegment_024_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 900 18 18, g32p_row19_traceSegment_024_0900_0018, g32p_row19_traceSegment_024_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 864 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 864 36 36, g32p_row19_traceSegment_024_0864_0036, g32p_row19_traceSegment_024_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 936 9 9, g32p_row19_traceSegment_024_0936_0009, g32p_row19_traceSegment_024_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 954 9 9, g32p_row19_traceSegment_024_0954_0009, g32p_row19_traceSegment_024_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 936 18 18, g32p_row19_traceSegment_024_0936_0018, g32p_row19_traceSegment_024_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 972 9 9, g32p_row19_traceSegment_024_0972_0009, g32p_row19_traceSegment_024_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 990 9 9, g32p_row19_traceSegment_024_0990_0009, g32p_row19_traceSegment_024_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 972 18 18, g32p_row19_traceSegment_024_0972_0018, g32p_row19_traceSegment_024_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 936 36 36, g32p_row19_traceSegment_024_0936_0036, g32p_row19_traceSegment_024_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 864 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 864 72 72, g32p_row19_traceSegment_024_0864_0072, g32p_row19_traceSegment_024_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1017 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1008 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1008 9 9, g32p_row19_traceSegment_024_1008_0009, g32p_row19_traceSegment_024_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1026 9 9, g32p_row19_traceSegment_024_1026_0009, g32p_row19_traceSegment_024_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 1008 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1008 18 18, g32p_row19_traceSegment_024_1008_0018, g32p_row19_traceSegment_024_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1044 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1044 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1044 9 9, g32p_row19_traceSegment_024_1044_0009, g32p_row19_traceSegment_024_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1062 9 9, g32p_row19_traceSegment_024_1062_0009, g32p_row19_traceSegment_024_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 1044 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1044 18 18, g32p_row19_traceSegment_024_1044_0018, g32p_row19_traceSegment_024_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 1008 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1008 36 36, g32p_row19_traceSegment_024_1008_0036, g32p_row19_traceSegment_024_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1080 9 9, g32p_row19_traceSegment_024_1080_0009, g32p_row19_traceSegment_024_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1098 9 9, g32p_row19_traceSegment_024_1098_0009, g32p_row19_traceSegment_024_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1080 18 18, g32p_row19_traceSegment_024_1080_0018, g32p_row19_traceSegment_024_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1116 9 9, g32p_row19_traceSegment_024_1116_0009, g32p_row19_traceSegment_024_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_024 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_024_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_024 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1134 9 9, g32p_row19_traceSegment_024_1134_0009, g32p_row19_traceSegment_024_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_024 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1116 18 18, g32p_row19_traceSegment_024_1116_0018, g32p_row19_traceSegment_024_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_024 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1080 36 36, g32p_row19_traceSegment_024_1080_0036, g32p_row19_traceSegment_024_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_024_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_024 1008 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 1008 72 72, g32p_row19_traceSegment_024_1008_0072, g32p_row19_traceSegment_024_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_024 864 288 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 864 144 144, g32p_row19_traceSegment_024_0864_0144, g32p_row19_traceSegment_024_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_024 576 576 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 576 288 288, g32p_row19_traceSegment_024_0576_0288, g32p_row19_traceSegment_024_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_024_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_024 0 1152 = [0, 0, 16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_024 0 576 576, g32p_row19_traceSegment_024_0000_0576, g32p_row19_traceSegment_024_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 24 = [0, 0, 16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_024_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row19_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 0) (g32p_literalTraceValue 18 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_000]
  decide +kernel

theorem g32p_row19_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 4) (g32p_literalTraceValue 18 4)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_004]
  decide +kernel

theorem g32p_row19_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 5) (g32p_literalTraceValue 18 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_005]
  decide +kernel

theorem g32p_row19_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 11) (g32p_literalTraceValue 18 11)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row19_traceCoefficients_011]
  decide +kernel

theorem g32p_row19_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 13) (g32p_literalTraceValue 18 13)
      [1, -1, 1] [0, 0, 2304, 2304] = true := by
  rw [g32p_row19_traceCoefficients_013]
  decide +kernel

theorem g32p_row19_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 18) (g32p_literalTraceValue 18 18)
      [1, -1, 1] [13824, 13824] = true := by
  rw [g32p_row19_traceCoefficients_018]
  decide +kernel

theorem g32p_row19_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 21) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 21) (g32p_literalTraceValue 18 21)
      [1, -1, 1] [-1152, 0, 1152, 1152] = true := by
  rw [g32p_row19_traceCoefficients_021]
  decide +kernel

theorem g32p_row19_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 24) (g32p_literalTraceValue 18 24)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row19_traceCoefficients_024]
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

private def g32p_row19_traceSegment_025 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 25 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_025_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 9 9, g32p_row19_traceSegment_025_0000_0009, g32p_row19_traceSegment_025_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 18 9 9, g32p_row19_traceSegment_025_0018_0009, g32p_row19_traceSegment_025_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 18 18, g32p_row19_traceSegment_025_0000_0018, g32p_row19_traceSegment_025_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 45 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 36 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 36 9 9, g32p_row19_traceSegment_025_0036_0009, g32p_row19_traceSegment_025_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 54 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 54 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 54 9 9, g32p_row19_traceSegment_025_0054_0009, g32p_row19_traceSegment_025_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 36 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 36 18 18, g32p_row19_traceSegment_025_0036_0018, g32p_row19_traceSegment_025_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 0 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 36 36, g32p_row19_traceSegment_025_0000_0036, g32p_row19_traceSegment_025_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 72 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 81 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 72 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 72 9 9, g32p_row19_traceSegment_025_0072_0009, g32p_row19_traceSegment_025_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 90 9 9, g32p_row19_traceSegment_025_0090_0009, g32p_row19_traceSegment_025_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 72 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 72 18 18, g32p_row19_traceSegment_025_0072_0018, g32p_row19_traceSegment_025_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 117 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 108 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 108 9 9, g32p_row19_traceSegment_025_0108_0009, g32p_row19_traceSegment_025_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 126 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 126 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 126 9 9, g32p_row19_traceSegment_025_0126_0009, g32p_row19_traceSegment_025_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 108 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 108 18 18, g32p_row19_traceSegment_025_0108_0018, g32p_row19_traceSegment_025_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 72 72 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 72 36 36, g32p_row19_traceSegment_025_0072_0036, g32p_row19_traceSegment_025_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 0 144 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 72 72, g32p_row19_traceSegment_025_0000_0072, g32p_row19_traceSegment_025_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 144 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 153 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 144 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 144 9 9, g32p_row19_traceSegment_025_0144_0009, g32p_row19_traceSegment_025_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 162 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 171 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 162 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 162 9 9, g32p_row19_traceSegment_025_0162_0009, g32p_row19_traceSegment_025_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 144 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 144 18 18, g32p_row19_traceSegment_025_0144_0018, g32p_row19_traceSegment_025_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 180 9 9, g32p_row19_traceSegment_025_0180_0009, g32p_row19_traceSegment_025_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 198 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 207 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 198 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 198 9 9, g32p_row19_traceSegment_025_0198_0009, g32p_row19_traceSegment_025_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 180 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 180 18 18, g32p_row19_traceSegment_025_0180_0018, g32p_row19_traceSegment_025_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 144 72 = [2, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 144 36 36, g32p_row19_traceSegment_025_0144_0036, g32p_row19_traceSegment_025_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 216 9 9, g32p_row19_traceSegment_025_0216_0009, g32p_row19_traceSegment_025_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 243 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 234 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 234 9 9, g32p_row19_traceSegment_025_0234_0009, g32p_row19_traceSegment_025_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 216 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 216 18 18, g32p_row19_traceSegment_025_0216_0018, g32p_row19_traceSegment_025_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 252 9 9, g32p_row19_traceSegment_025_0252_0009, g32p_row19_traceSegment_025_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 279 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 270 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 270 9 9, g32p_row19_traceSegment_025_0270_0009, g32p_row19_traceSegment_025_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 252 18 18, g32p_row19_traceSegment_025_0252_0018, g32p_row19_traceSegment_025_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 216 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 216 36 36, g32p_row19_traceSegment_025_0216_0036, g32p_row19_traceSegment_025_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 144 144 = [2, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 144 72 72, g32p_row19_traceSegment_025_0144_0072, g32p_row19_traceSegment_025_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_025 0 288 = [2, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 144 144, g32p_row19_traceSegment_025_0000_0144, g32p_row19_traceSegment_025_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 297 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 288 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 288 9 9, g32p_row19_traceSegment_025_0288_0009, g32p_row19_traceSegment_025_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 306 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 306 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 306 9 9, g32p_row19_traceSegment_025_0306_0009, g32p_row19_traceSegment_025_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 288 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 288 18 18, g32p_row19_traceSegment_025_0288_0018, g32p_row19_traceSegment_025_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 324 9 9, g32p_row19_traceSegment_025_0324_0009, g32p_row19_traceSegment_025_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 351 9 = [1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 342 18 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 342 9 9, g32p_row19_traceSegment_025_0342_0009, g32p_row19_traceSegment_025_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 324 36 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 324 18 18, g32p_row19_traceSegment_025_0324_0018, g32p_row19_traceSegment_025_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 288 72 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 288 36 36, g32p_row19_traceSegment_025_0288_0036, g32p_row19_traceSegment_025_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 360 9 = [1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 369 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 360 18 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 360 9 9, g32p_row19_traceSegment_025_0360_0009, g32p_row19_traceSegment_025_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 378 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 378 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 378 9 9, g32p_row19_traceSegment_025_0378_0009, g32p_row19_traceSegment_025_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 360 36 = [5, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 360 18 18, g32p_row19_traceSegment_025_0360_0018, g32p_row19_traceSegment_025_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 405 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 396 18 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 396 9 9, g32p_row19_traceSegment_025_0396_0009, g32p_row19_traceSegment_025_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 414 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 414 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 414 9 9, g32p_row19_traceSegment_025_0414_0009, g32p_row19_traceSegment_025_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 396 36 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 396 18 18, g32p_row19_traceSegment_025_0396_0018, g32p_row19_traceSegment_025_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 360 72 = [7, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 360 36 36, g32p_row19_traceSegment_025_0360_0036, g32p_row19_traceSegment_025_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 288 144 = [8, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 288 72 72, g32p_row19_traceSegment_025_0288_0072, g32p_row19_traceSegment_025_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 432 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 441 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 432 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 432 9 9, g32p_row19_traceSegment_025_0432_0009, g32p_row19_traceSegment_025_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 450 9 9, g32p_row19_traceSegment_025_0450_0009, g32p_row19_traceSegment_025_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 432 36 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 432 18 18, g32p_row19_traceSegment_025_0432_0018, g32p_row19_traceSegment_025_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 468 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 477 9 = [3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 468 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 468 9 9, g32p_row19_traceSegment_025_0468_0009, g32p_row19_traceSegment_025_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 486 9 9, g32p_row19_traceSegment_025_0486_0009, g32p_row19_traceSegment_025_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 468 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 468 18 18, g32p_row19_traceSegment_025_0468_0018, g32p_row19_traceSegment_025_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 432 72 = [7, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 432 36 36, g32p_row19_traceSegment_025_0432_0036, g32p_row19_traceSegment_025_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 504 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 513 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 504 18 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 504 9 9, g32p_row19_traceSegment_025_0504_0009, g32p_row19_traceSegment_025_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 522 9 9, g32p_row19_traceSegment_025_0522_0009, g32p_row19_traceSegment_025_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 504 36 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 504 18 18, g32p_row19_traceSegment_025_0504_0018, g32p_row19_traceSegment_025_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 540 9 9, g32p_row19_traceSegment_025_0540_0009, g32p_row19_traceSegment_025_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 567 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 558 9 9, g32p_row19_traceSegment_025_0558_0009, g32p_row19_traceSegment_025_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 540 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 540 18 18, g32p_row19_traceSegment_025_0540_0018, g32p_row19_traceSegment_025_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 504 72 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 504 36 36, g32p_row19_traceSegment_025_0504_0036, g32p_row19_traceSegment_025_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 432 144 = [9, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 432 72 72, g32p_row19_traceSegment_025_0432_0072, g32p_row19_traceSegment_025_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_025 288 288 = [17, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 288 144 144, g32p_row19_traceSegment_025_0288_0144, g32p_row19_traceSegment_025_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_025 0 576 = [19, 23] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 288 288, g32p_row19_traceSegment_025_0000_0288, g32p_row19_traceSegment_025_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 585 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 576 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 576 9 9, g32p_row19_traceSegment_025_0576_0009, g32p_row19_traceSegment_025_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 594 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 594 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 594 9 9, g32p_row19_traceSegment_025_0594_0009, g32p_row19_traceSegment_025_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 576 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 576 18 18, g32p_row19_traceSegment_025_0576_0018, g32p_row19_traceSegment_025_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 612 9 9, g32p_row19_traceSegment_025_0612_0009, g32p_row19_traceSegment_025_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 639 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 630 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 630 9 9, g32p_row19_traceSegment_025_0630_0009, g32p_row19_traceSegment_025_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 612 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 612 18 18, g32p_row19_traceSegment_025_0612_0018, g32p_row19_traceSegment_025_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 576 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 576 36 36, g32p_row19_traceSegment_025_0576_0036, g32p_row19_traceSegment_025_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 657 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 648 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 648 9 9, g32p_row19_traceSegment_025_0648_0009, g32p_row19_traceSegment_025_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 666 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 666 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 666 9 9, g32p_row19_traceSegment_025_0666_0009, g32p_row19_traceSegment_025_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 648 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 648 18 18, g32p_row19_traceSegment_025_0648_0018, g32p_row19_traceSegment_025_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 693 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 684 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 684 9 9, g32p_row19_traceSegment_025_0684_0009, g32p_row19_traceSegment_025_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 702 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 702 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 702 9 9, g32p_row19_traceSegment_025_0702_0009, g32p_row19_traceSegment_025_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 684 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 684 18 18, g32p_row19_traceSegment_025_0684_0018, g32p_row19_traceSegment_025_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 648 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 648 36 36, g32p_row19_traceSegment_025_0648_0036, g32p_row19_traceSegment_025_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 576 144 = [4, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 576 72 72, g32p_row19_traceSegment_025_0576_0072, g32p_row19_traceSegment_025_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 729 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 720 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 720 9 9, g32p_row19_traceSegment_025_0720_0009, g32p_row19_traceSegment_025_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 738 9 9, g32p_row19_traceSegment_025_0738_0009, g32p_row19_traceSegment_025_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 720 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 720 18 18, g32p_row19_traceSegment_025_0720_0018, g32p_row19_traceSegment_025_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 756 9 9, g32p_row19_traceSegment_025_0756_0009, g32p_row19_traceSegment_025_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 774 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 774 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 774 9 9, g32p_row19_traceSegment_025_0774_0009, g32p_row19_traceSegment_025_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 756 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 756 18 18, g32p_row19_traceSegment_025_0756_0018, g32p_row19_traceSegment_025_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 720 72 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 720 36 36, g32p_row19_traceSegment_025_0720_0036, g32p_row19_traceSegment_025_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 792 9 9, g32p_row19_traceSegment_025_0792_0009, g32p_row19_traceSegment_025_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 810 9 9, g32p_row19_traceSegment_025_0810_0009, g32p_row19_traceSegment_025_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 792 18 18, g32p_row19_traceSegment_025_0792_0018, g32p_row19_traceSegment_025_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 837 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 828 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 828 9 9, g32p_row19_traceSegment_025_0828_0009, g32p_row19_traceSegment_025_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 846 9 9, g32p_row19_traceSegment_025_0846_0009, g32p_row19_traceSegment_025_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 828 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 828 18 18, g32p_row19_traceSegment_025_0828_0018, g32p_row19_traceSegment_025_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 792 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 792 36 36, g32p_row19_traceSegment_025_0792_0036, g32p_row19_traceSegment_025_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 720 144 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 720 72 72, g32p_row19_traceSegment_025_0720_0072, g32p_row19_traceSegment_025_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_025 576 288 = [5, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 576 144 144, g32p_row19_traceSegment_025_0576_0144, g32p_row19_traceSegment_025_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 864 9 9, g32p_row19_traceSegment_025_0864_0009, g32p_row19_traceSegment_025_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 882 9 9, g32p_row19_traceSegment_025_0882_0009, g32p_row19_traceSegment_025_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 864 18 18, g32p_row19_traceSegment_025_0864_0018, g32p_row19_traceSegment_025_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 900 9 9, g32p_row19_traceSegment_025_0900_0009, g32p_row19_traceSegment_025_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 918 9 9, g32p_row19_traceSegment_025_0918_0009, g32p_row19_traceSegment_025_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 900 18 18, g32p_row19_traceSegment_025_0900_0018, g32p_row19_traceSegment_025_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 864 36 36, g32p_row19_traceSegment_025_0864_0036, g32p_row19_traceSegment_025_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 936 9 9, g32p_row19_traceSegment_025_0936_0009, g32p_row19_traceSegment_025_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 954 9 9, g32p_row19_traceSegment_025_0954_0009, g32p_row19_traceSegment_025_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 936 18 18, g32p_row19_traceSegment_025_0936_0018, g32p_row19_traceSegment_025_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 972 9 9, g32p_row19_traceSegment_025_0972_0009, g32p_row19_traceSegment_025_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 990 9 9, g32p_row19_traceSegment_025_0990_0009, g32p_row19_traceSegment_025_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 972 18 18, g32p_row19_traceSegment_025_0972_0018, g32p_row19_traceSegment_025_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 936 36 36, g32p_row19_traceSegment_025_0936_0036, g32p_row19_traceSegment_025_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 864 72 72, g32p_row19_traceSegment_025_0864_0072, g32p_row19_traceSegment_025_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1008 9 9, g32p_row19_traceSegment_025_1008_0009, g32p_row19_traceSegment_025_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1026 9 9, g32p_row19_traceSegment_025_1026_0009, g32p_row19_traceSegment_025_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1008 18 18, g32p_row19_traceSegment_025_1008_0018, g32p_row19_traceSegment_025_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1044 9 9, g32p_row19_traceSegment_025_1044_0009, g32p_row19_traceSegment_025_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1062 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1071 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1062 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1062 9 9, g32p_row19_traceSegment_025_1062_0009, g32p_row19_traceSegment_025_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 1044 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1044 18 18, g32p_row19_traceSegment_025_1044_0018, g32p_row19_traceSegment_025_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 1008 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1008 36 36, g32p_row19_traceSegment_025_1008_0036, g32p_row19_traceSegment_025_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1080 9 = [1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1089 9 = [1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1080 18 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1080 9 9, g32p_row19_traceSegment_025_1080_0009, g32p_row19_traceSegment_025_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1098 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1098 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1098 9 9, g32p_row19_traceSegment_025_1098_0009, g32p_row19_traceSegment_025_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 1080 36 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1080 18 18, g32p_row19_traceSegment_025_1080_0018, g32p_row19_traceSegment_025_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1116 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1125 9 = [1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1116 18 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1116 9 9, g32p_row19_traceSegment_025_1116_0009, g32p_row19_traceSegment_025_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1134 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_025 1143 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_025_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_025 1134 18 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1134 9 9, g32p_row19_traceSegment_025_1134_0009, g32p_row19_traceSegment_025_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_025 1116 36 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1116 18 18, g32p_row19_traceSegment_025_1116_0018, g32p_row19_traceSegment_025_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_025 1080 72 = [6, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1080 36 36, g32p_row19_traceSegment_025_1080_0036, g32p_row19_traceSegment_025_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_025_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_025 1008 144 = [8, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 1008 72 72, g32p_row19_traceSegment_025_1008_0072, g32p_row19_traceSegment_025_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_025 864 288 = [8, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 864 144 144, g32p_row19_traceSegment_025_0864_0144, g32p_row19_traceSegment_025_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_025 576 576 = [13, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 576 288 288, g32p_row19_traceSegment_025_0576_0288, g32p_row19_traceSegment_025_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_025_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_025 0 1152 = [32, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_025 0 576 576, g32p_row19_traceSegment_025_0000_0576, g32p_row19_traceSegment_025_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 25 = [32, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_025_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_029 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 29 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_029_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 9 9, g32p_row19_traceSegment_029_0000_0009, g32p_row19_traceSegment_029_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 18 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 27 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 18 18 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 18 9 9, g32p_row19_traceSegment_029_0018_0009, g32p_row19_traceSegment_029_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 0 36 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 18 18, g32p_row19_traceSegment_029_0000_0018, g32p_row19_traceSegment_029_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 45 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 36 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 36 9 9, g32p_row19_traceSegment_029_0036_0009, g32p_row19_traceSegment_029_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 54 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 63 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 54 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 54 9 9, g32p_row19_traceSegment_029_0054_0009, g32p_row19_traceSegment_029_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 36 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 36 18 18, g32p_row19_traceSegment_029_0036_0018, g32p_row19_traceSegment_029_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 0 72 = [6, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 36 36, g32p_row19_traceSegment_029_0000_0036, g32p_row19_traceSegment_029_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 72 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 81 9 = [1, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 72 18 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 72 9 9, g32p_row19_traceSegment_029_0072_0009, g32p_row19_traceSegment_029_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 90 9 9, g32p_row19_traceSegment_029_0090_0009, g32p_row19_traceSegment_029_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 72 36 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 72 18 18, g32p_row19_traceSegment_029_0072_0018, g32p_row19_traceSegment_029_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 108 9 9, g32p_row19_traceSegment_029_0108_0009, g32p_row19_traceSegment_029_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 126 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 126 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 126 9 9, g32p_row19_traceSegment_029_0126_0009, g32p_row19_traceSegment_029_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 108 18 18, g32p_row19_traceSegment_029_0108_0018, g32p_row19_traceSegment_029_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 72 72 = [3, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 72 36 36, g32p_row19_traceSegment_029_0072_0036, g32p_row19_traceSegment_029_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 0 144 = [9, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 72 72, g32p_row19_traceSegment_029_0000_0072, g32p_row19_traceSegment_029_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 144 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 144 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 144 9 9, g32p_row19_traceSegment_029_0144_0009, g32p_row19_traceSegment_029_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 162 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 162 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 162 9 9, g32p_row19_traceSegment_029_0162_0009, g32p_row19_traceSegment_029_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 144 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 144 18 18, g32p_row19_traceSegment_029_0144_0018, g32p_row19_traceSegment_029_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 189 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 180 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 180 9 9, g32p_row19_traceSegment_029_0180_0009, g32p_row19_traceSegment_029_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 198 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 207 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 198 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 198 9 9, g32p_row19_traceSegment_029_0198_0009, g32p_row19_traceSegment_029_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 180 36 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 180 18 18, g32p_row19_traceSegment_029_0180_0018, g32p_row19_traceSegment_029_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 144 72 = [3, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 144 36 36, g32p_row19_traceSegment_029_0144_0036, g32p_row19_traceSegment_029_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 216 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 225 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 216 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 216 9 9, g32p_row19_traceSegment_029_0216_0009, g32p_row19_traceSegment_029_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 234 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 243 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 234 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 234 9 9, g32p_row19_traceSegment_029_0234_0009, g32p_row19_traceSegment_029_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 216 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 216 18 18, g32p_row19_traceSegment_029_0216_0018, g32p_row19_traceSegment_029_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 261 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 252 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 252 9 9, g32p_row19_traceSegment_029_0252_0009, g32p_row19_traceSegment_029_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 270 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 279 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 270 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 270 9 9, g32p_row19_traceSegment_029_0270_0009, g32p_row19_traceSegment_029_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 252 36 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 252 18 18, g32p_row19_traceSegment_029_0252_0018, g32p_row19_traceSegment_029_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 216 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 216 36 36, g32p_row19_traceSegment_029_0216_0036, g32p_row19_traceSegment_029_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 144 144 = [3, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 144 72 72, g32p_row19_traceSegment_029_0144_0072, g32p_row19_traceSegment_029_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_029 0 288 = [12, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 144 144, g32p_row19_traceSegment_029_0000_0144, g32p_row19_traceSegment_029_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 288 9 9, g32p_row19_traceSegment_029_0288_0009, g32p_row19_traceSegment_029_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 306 9 9, g32p_row19_traceSegment_029_0306_0009, g32p_row19_traceSegment_029_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 288 18 18, g32p_row19_traceSegment_029_0288_0018, g32p_row19_traceSegment_029_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 324 9 9, g32p_row19_traceSegment_029_0324_0009, g32p_row19_traceSegment_029_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 342 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 351 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 342 18 = [2, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 342 9 9, g32p_row19_traceSegment_029_0342_0009, g32p_row19_traceSegment_029_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 324 36 = [2, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 324 18 18, g32p_row19_traceSegment_029_0324_0018, g32p_row19_traceSegment_029_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 288 72 = [2, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 288 36 36, g32p_row19_traceSegment_029_0288_0036, g32p_row19_traceSegment_029_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 369 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 360 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 360 9 9, g32p_row19_traceSegment_029_0360_0009, g32p_row19_traceSegment_029_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 378 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 387 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 378 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 378 9 9, g32p_row19_traceSegment_029_0378_0009, g32p_row19_traceSegment_029_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 360 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 360 18 18, g32p_row19_traceSegment_029_0360_0018, g32p_row19_traceSegment_029_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 396 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 405 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 396 18 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 396 9 9, g32p_row19_traceSegment_029_0396_0009, g32p_row19_traceSegment_029_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 423 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 414 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 414 9 9, g32p_row19_traceSegment_029_0414_0009, g32p_row19_traceSegment_029_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 396 36 = [1, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 396 18 18, g32p_row19_traceSegment_029_0396_0018, g32p_row19_traceSegment_029_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 360 72 = [4, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 360 36 36, g32p_row19_traceSegment_029_0360_0036, g32p_row19_traceSegment_029_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 288 144 = [6, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 288 72 72, g32p_row19_traceSegment_029_0288_0072, g32p_row19_traceSegment_029_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 432 9 9, g32p_row19_traceSegment_029_0432_0009, g32p_row19_traceSegment_029_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 450 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 459 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 450 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 450 9 9, g32p_row19_traceSegment_029_0450_0009, g32p_row19_traceSegment_029_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 432 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 432 18 18, g32p_row19_traceSegment_029_0432_0018, g32p_row19_traceSegment_029_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 468 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 477 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 468 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 468 9 9, g32p_row19_traceSegment_029_0468_0009, g32p_row19_traceSegment_029_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 486 9 9, g32p_row19_traceSegment_029_0486_0009, g32p_row19_traceSegment_029_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 468 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 468 18 18, g32p_row19_traceSegment_029_0468_0018, g32p_row19_traceSegment_029_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 432 72 = [2, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 432 36 36, g32p_row19_traceSegment_029_0432_0036, g32p_row19_traceSegment_029_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 504 9 9, g32p_row19_traceSegment_029_0504_0009, g32p_row19_traceSegment_029_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 522 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 522 9 9, g32p_row19_traceSegment_029_0522_0009, g32p_row19_traceSegment_029_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 504 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 504 18 18, g32p_row19_traceSegment_029_0504_0018, g32p_row19_traceSegment_029_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 540 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 540 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 540 9 9, g32p_row19_traceSegment_029_0540_0009, g32p_row19_traceSegment_029_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 558 9 9, g32p_row19_traceSegment_029_0558_0009, g32p_row19_traceSegment_029_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 540 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 540 18 18, g32p_row19_traceSegment_029_0540_0018, g32p_row19_traceSegment_029_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 504 72 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 504 36 36, g32p_row19_traceSegment_029_0504_0036, g32p_row19_traceSegment_029_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 432 144 = [3, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 432 72 72, g32p_row19_traceSegment_029_0432_0072, g32p_row19_traceSegment_029_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_029 288 288 = [9, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 288 144 144, g32p_row19_traceSegment_029_0288_0144, g32p_row19_traceSegment_029_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_029 0 576 = [21, 0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 288 288, g32p_row19_traceSegment_029_0000_0288, g32p_row19_traceSegment_029_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 576 9 9, g32p_row19_traceSegment_029_0576_0009, g32p_row19_traceSegment_029_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 594 9 9, g32p_row19_traceSegment_029_0594_0009, g32p_row19_traceSegment_029_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 576 18 18, g32p_row19_traceSegment_029_0576_0018, g32p_row19_traceSegment_029_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 612 9 9, g32p_row19_traceSegment_029_0612_0009, g32p_row19_traceSegment_029_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 630 9 9, g32p_row19_traceSegment_029_0630_0009, g32p_row19_traceSegment_029_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 612 18 18, g32p_row19_traceSegment_029_0612_0018, g32p_row19_traceSegment_029_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 576 36 36, g32p_row19_traceSegment_029_0576_0036, g32p_row19_traceSegment_029_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 648 9 9, g32p_row19_traceSegment_029_0648_0009, g32p_row19_traceSegment_029_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 666 9 9, g32p_row19_traceSegment_029_0666_0009, g32p_row19_traceSegment_029_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 648 18 18, g32p_row19_traceSegment_029_0648_0018, g32p_row19_traceSegment_029_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 684 9 9, g32p_row19_traceSegment_029_0684_0009, g32p_row19_traceSegment_029_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 702 9 9, g32p_row19_traceSegment_029_0702_0009, g32p_row19_traceSegment_029_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 684 18 18, g32p_row19_traceSegment_029_0684_0018, g32p_row19_traceSegment_029_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 648 36 36, g32p_row19_traceSegment_029_0648_0036, g32p_row19_traceSegment_029_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 576 72 72, g32p_row19_traceSegment_029_0576_0072, g32p_row19_traceSegment_029_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 720 9 9, g32p_row19_traceSegment_029_0720_0009, g32p_row19_traceSegment_029_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 738 9 9, g32p_row19_traceSegment_029_0738_0009, g32p_row19_traceSegment_029_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 720 18 18, g32p_row19_traceSegment_029_0720_0018, g32p_row19_traceSegment_029_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 756 9 9, g32p_row19_traceSegment_029_0756_0009, g32p_row19_traceSegment_029_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 774 9 9, g32p_row19_traceSegment_029_0774_0009, g32p_row19_traceSegment_029_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 756 18 18, g32p_row19_traceSegment_029_0756_0018, g32p_row19_traceSegment_029_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 720 36 36, g32p_row19_traceSegment_029_0720_0036, g32p_row19_traceSegment_029_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 792 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 792 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 792 9 9, g32p_row19_traceSegment_029_0792_0009, g32p_row19_traceSegment_029_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 810 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 810 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 810 9 9, g32p_row19_traceSegment_029_0810_0009, g32p_row19_traceSegment_029_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 792 36 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 792 18 18, g32p_row19_traceSegment_029_0792_0018, g32p_row19_traceSegment_029_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 828 9 9, g32p_row19_traceSegment_029_0828_0009, g32p_row19_traceSegment_029_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 846 9 9, g32p_row19_traceSegment_029_0846_0009, g32p_row19_traceSegment_029_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 828 18 18, g32p_row19_traceSegment_029_0828_0018, g32p_row19_traceSegment_029_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 792 72 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 792 36 36, g32p_row19_traceSegment_029_0792_0036, g32p_row19_traceSegment_029_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 720 144 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 720 72 72, g32p_row19_traceSegment_029_0720_0072, g32p_row19_traceSegment_029_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_029 576 288 = [1, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 576 144 144, g32p_row19_traceSegment_029_0576_0144, g32p_row19_traceSegment_029_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 864 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 864 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 864 9 9, g32p_row19_traceSegment_029_0864_0009, g32p_row19_traceSegment_029_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 882 9 9, g32p_row19_traceSegment_029_0882_0009, g32p_row19_traceSegment_029_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 864 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 864 18 18, g32p_row19_traceSegment_029_0864_0018, g32p_row19_traceSegment_029_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 900 9 9, g32p_row19_traceSegment_029_0900_0009, g32p_row19_traceSegment_029_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 918 9 9, g32p_row19_traceSegment_029_0918_0009, g32p_row19_traceSegment_029_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 900 18 18, g32p_row19_traceSegment_029_0900_0018, g32p_row19_traceSegment_029_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 864 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 864 36 36, g32p_row19_traceSegment_029_0864_0036, g32p_row19_traceSegment_029_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 936 9 9, g32p_row19_traceSegment_029_0936_0009, g32p_row19_traceSegment_029_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 954 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 963 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 954 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 954 9 9, g32p_row19_traceSegment_029_0954_0009, g32p_row19_traceSegment_029_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 936 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 936 18 18, g32p_row19_traceSegment_029_0936_0018, g32p_row19_traceSegment_029_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 981 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 972 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 972 9 9, g32p_row19_traceSegment_029_0972_0009, g32p_row19_traceSegment_029_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 990 9 9, g32p_row19_traceSegment_029_0990_0009, g32p_row19_traceSegment_029_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 972 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 972 18 18, g32p_row19_traceSegment_029_0972_0018, g32p_row19_traceSegment_029_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 936 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 936 36 36, g32p_row19_traceSegment_029_0936_0036, g32p_row19_traceSegment_029_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 864 144 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 864 72 72, g32p_row19_traceSegment_029_0864_0072, g32p_row19_traceSegment_029_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1008 9 9, g32p_row19_traceSegment_029_1008_0009, g32p_row19_traceSegment_029_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1026 9 9, g32p_row19_traceSegment_029_1026_0009, g32p_row19_traceSegment_029_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1008 18 18, g32p_row19_traceSegment_029_1008_0018, g32p_row19_traceSegment_029_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1053 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1044 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1044 9 9, g32p_row19_traceSegment_029_1044_0009, g32p_row19_traceSegment_029_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1062 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1071 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1062 18 = [1, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1062 9 9, g32p_row19_traceSegment_029_1062_0009, g32p_row19_traceSegment_029_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 1044 36 = [1, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1044 18 18, g32p_row19_traceSegment_029_1044_0018, g32p_row19_traceSegment_029_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 1008 72 = [1, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1008 36 36, g32p_row19_traceSegment_029_1008_0036, g32p_row19_traceSegment_029_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1080 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1089 9 = [3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1080 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1080 9 9, g32p_row19_traceSegment_029_1080_0009, g32p_row19_traceSegment_029_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1098 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1107 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1098 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1098 9 9, g32p_row19_traceSegment_029_1098_0009, g32p_row19_traceSegment_029_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 1080 36 = [6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1080 18 18, g32p_row19_traceSegment_029_1080_0018, g32p_row19_traceSegment_029_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1116 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1116 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1116 9 9, g32p_row19_traceSegment_029_1116_0009, g32p_row19_traceSegment_029_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1134 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_029 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_029_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_029 1134 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1134 9 9, g32p_row19_traceSegment_029_1134_0009, g32p_row19_traceSegment_029_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_029 1116 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1116 18 18, g32p_row19_traceSegment_029_1116_0018, g32p_row19_traceSegment_029_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_029 1080 72 = [9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1080 36 36, g32p_row19_traceSegment_029_1080_0036, g32p_row19_traceSegment_029_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_029_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_029 1008 144 = [10, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 1008 72 72, g32p_row19_traceSegment_029_1008_0072, g32p_row19_traceSegment_029_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_029 864 288 = [10, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 864 144 144, g32p_row19_traceSegment_029_0864_0144, g32p_row19_traceSegment_029_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_029 576 576 = [11, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 576 288 288, g32p_row19_traceSegment_029_0576_0288, g32p_row19_traceSegment_029_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_029_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_029 0 1152 = [32, 0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_029 0 576 576, g32p_row19_traceSegment_029_0000_0576, g32p_row19_traceSegment_029_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 29 = [32, 0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_029_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_030 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 30 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_030_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 9 9, g32p_row19_traceSegment_030_0000_0009, g32p_row19_traceSegment_030_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 18 9 9, g32p_row19_traceSegment_030_0018_0009, g32p_row19_traceSegment_030_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 18 18, g32p_row19_traceSegment_030_0000_0018, g32p_row19_traceSegment_030_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 36 9 9, g32p_row19_traceSegment_030_0036_0009, g32p_row19_traceSegment_030_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 54 9 9, g32p_row19_traceSegment_030_0054_0009, g32p_row19_traceSegment_030_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 36 18 18, g32p_row19_traceSegment_030_0036_0018, g32p_row19_traceSegment_030_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 36 36, g32p_row19_traceSegment_030_0000_0036, g32p_row19_traceSegment_030_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 72 9 9, g32p_row19_traceSegment_030_0072_0009, g32p_row19_traceSegment_030_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 90 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 99 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 90 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 90 9 9, g32p_row19_traceSegment_030_0090_0009, g32p_row19_traceSegment_030_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 72 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 72 18 18, g32p_row19_traceSegment_030_0072_0018, g32p_row19_traceSegment_030_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 108 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 117 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 108 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 108 9 9, g32p_row19_traceSegment_030_0108_0009, g32p_row19_traceSegment_030_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 126 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 135 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 126 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 126 9 9, g32p_row19_traceSegment_030_0126_0009, g32p_row19_traceSegment_030_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 108 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 108 18 18, g32p_row19_traceSegment_030_0108_0018, g32p_row19_traceSegment_030_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 72 72 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 72 36 36, g32p_row19_traceSegment_030_0072_0036, g32p_row19_traceSegment_030_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 0 144 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 72 72, g32p_row19_traceSegment_030_0000_0072, g32p_row19_traceSegment_030_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 144 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 144 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 144 9 9, g32p_row19_traceSegment_030_0144_0009, g32p_row19_traceSegment_030_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 171 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 162 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 162 9 9, g32p_row19_traceSegment_030_0162_0009, g32p_row19_traceSegment_030_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 144 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 144 18 18, g32p_row19_traceSegment_030_0144_0018, g32p_row19_traceSegment_030_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 180 9 9, g32p_row19_traceSegment_030_0180_0009, g32p_row19_traceSegment_030_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 207 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 198 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 198 9 9, g32p_row19_traceSegment_030_0198_0009, g32p_row19_traceSegment_030_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 180 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 180 18 18, g32p_row19_traceSegment_030_0180_0018, g32p_row19_traceSegment_030_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 144 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 144 36 36, g32p_row19_traceSegment_030_0144_0036, g32p_row19_traceSegment_030_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 216 9 9, g32p_row19_traceSegment_030_0216_0009, g32p_row19_traceSegment_030_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 234 9 = [0, 0, 0, 2, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 234 18 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 234 9 9, g32p_row19_traceSegment_030_0234_0009, g32p_row19_traceSegment_030_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 216 36 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 216 18 18, g32p_row19_traceSegment_030_0216_0018, g32p_row19_traceSegment_030_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 252 9 = [0, 0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 261 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 252 18 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 252 9 9, g32p_row19_traceSegment_030_0252_0009, g32p_row19_traceSegment_030_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 270 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 279 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 270 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 270 9 9, g32p_row19_traceSegment_030_0270_0009, g32p_row19_traceSegment_030_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 252 36 = [0, 0, 0, 3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 252 18 18, g32p_row19_traceSegment_030_0252_0018, g32p_row19_traceSegment_030_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 216 72 = [0, 0, 0, 5, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 216 36 36, g32p_row19_traceSegment_030_0216_0036, g32p_row19_traceSegment_030_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 144 144 = [0, 0, 0, 8, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 144 72 72, g32p_row19_traceSegment_030_0144_0072, g32p_row19_traceSegment_030_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_030 0 288 = [0, 0, 0, 16, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 144 144, g32p_row19_traceSegment_030_0000_0144, g32p_row19_traceSegment_030_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 288 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 288 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 288 9 9, g32p_row19_traceSegment_030_0288_0009, g32p_row19_traceSegment_030_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 306 9 9, g32p_row19_traceSegment_030_0306_0009, g32p_row19_traceSegment_030_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 288 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 288 18 18, g32p_row19_traceSegment_030_0288_0018, g32p_row19_traceSegment_030_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 324 9 9, g32p_row19_traceSegment_030_0324_0009, g32p_row19_traceSegment_030_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 342 9 9, g32p_row19_traceSegment_030_0342_0009, g32p_row19_traceSegment_030_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 324 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 324 18 18, g32p_row19_traceSegment_030_0324_0018, g32p_row19_traceSegment_030_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 288 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 288 36 36, g32p_row19_traceSegment_030_0288_0036, g32p_row19_traceSegment_030_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 360 9 9, g32p_row19_traceSegment_030_0360_0009, g32p_row19_traceSegment_030_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 378 9 9, g32p_row19_traceSegment_030_0378_0009, g32p_row19_traceSegment_030_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 360 18 18, g32p_row19_traceSegment_030_0360_0018, g32p_row19_traceSegment_030_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 396 9 9, g32p_row19_traceSegment_030_0396_0009, g32p_row19_traceSegment_030_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 414 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 423 9 = [0, 0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 414 18 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 414 9 9, g32p_row19_traceSegment_030_0414_0009, g32p_row19_traceSegment_030_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 396 36 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 396 18 18, g32p_row19_traceSegment_030_0396_0018, g32p_row19_traceSegment_030_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 360 72 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 360 36 36, g32p_row19_traceSegment_030_0360_0036, g32p_row19_traceSegment_030_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 288 144 = [0, 0, 0, 1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 288 72 72, g32p_row19_traceSegment_030_0288_0072, g32p_row19_traceSegment_030_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 432 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 432 9 9, g32p_row19_traceSegment_030_0432_0009, g32p_row19_traceSegment_030_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 450 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 450 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 450 9 9, g32p_row19_traceSegment_030_0450_0009, g32p_row19_traceSegment_030_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 432 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 432 18 18, g32p_row19_traceSegment_030_0432_0018, g32p_row19_traceSegment_030_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 468 9 9, g32p_row19_traceSegment_030_0468_0009, g32p_row19_traceSegment_030_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 486 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 495 9 = [0, 0, 0, 1, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 486 18 = [0, 0, 0, 1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 486 9 9, g32p_row19_traceSegment_030_0486_0009, g32p_row19_traceSegment_030_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 468 36 = [0, 0, 0, 1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 468 18 18, g32p_row19_traceSegment_030_0468_0018, g32p_row19_traceSegment_030_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 432 72 = [0, 0, 0, 1, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 432 36 36, g32p_row19_traceSegment_030_0432_0036, g32p_row19_traceSegment_030_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 504 9 9, g32p_row19_traceSegment_030_0504_0009, g32p_row19_traceSegment_030_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 531 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 522 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 522 9 9, g32p_row19_traceSegment_030_0522_0009, g32p_row19_traceSegment_030_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 504 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 504 18 18, g32p_row19_traceSegment_030_0504_0018, g32p_row19_traceSegment_030_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 540 9 9, g32p_row19_traceSegment_030_0540_0009, g32p_row19_traceSegment_030_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 558 9 9, g32p_row19_traceSegment_030_0558_0009, g32p_row19_traceSegment_030_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 540 18 18, g32p_row19_traceSegment_030_0540_0018, g32p_row19_traceSegment_030_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 504 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 504 36 36, g32p_row19_traceSegment_030_0504_0036, g32p_row19_traceSegment_030_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 432 144 = [0, 0, 0, 1, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 432 72 72, g32p_row19_traceSegment_030_0432_0072, g32p_row19_traceSegment_030_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_030 288 288 = [0, 0, 0, 2, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 288 144 144, g32p_row19_traceSegment_030_0288_0144, g32p_row19_traceSegment_030_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_030 0 576 = [0, 0, 0, 18, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 288 288, g32p_row19_traceSegment_030_0000_0288, g32p_row19_traceSegment_030_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 576 9 9, g32p_row19_traceSegment_030_0576_0009, g32p_row19_traceSegment_030_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 594 9 9, g32p_row19_traceSegment_030_0594_0009, g32p_row19_traceSegment_030_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 576 18 18, g32p_row19_traceSegment_030_0576_0018, g32p_row19_traceSegment_030_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 621 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 612 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 612 9 9, g32p_row19_traceSegment_030_0612_0009, g32p_row19_traceSegment_030_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 630 9 9, g32p_row19_traceSegment_030_0630_0009, g32p_row19_traceSegment_030_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 612 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 612 18 18, g32p_row19_traceSegment_030_0612_0018, g32p_row19_traceSegment_030_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 576 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 576 36 36, g32p_row19_traceSegment_030_0576_0036, g32p_row19_traceSegment_030_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 648 9 9, g32p_row19_traceSegment_030_0648_0009, g32p_row19_traceSegment_030_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 675 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 666 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 666 9 9, g32p_row19_traceSegment_030_0666_0009, g32p_row19_traceSegment_030_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 648 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 648 18 18, g32p_row19_traceSegment_030_0648_0018, g32p_row19_traceSegment_030_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 684 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 684 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 684 9 9, g32p_row19_traceSegment_030_0684_0009, g32p_row19_traceSegment_030_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 702 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 702 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 702 9 9, g32p_row19_traceSegment_030_0702_0009, g32p_row19_traceSegment_030_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 684 36 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 684 18 18, g32p_row19_traceSegment_030_0684_0018, g32p_row19_traceSegment_030_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 648 72 = [0, 0, 0, 1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 648 36 36, g32p_row19_traceSegment_030_0648_0036, g32p_row19_traceSegment_030_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 576 144 = [0, 0, 0, 3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 576 72 72, g32p_row19_traceSegment_030_0576_0072, g32p_row19_traceSegment_030_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 720 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 720 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 720 9 9, g32p_row19_traceSegment_030_0720_0009, g32p_row19_traceSegment_030_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 747 9 = [0, 0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 738 18 = [0, 0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 738 9 9, g32p_row19_traceSegment_030_0738_0009, g32p_row19_traceSegment_030_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 720 36 = [0, 0, 0, 3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 720 18 18, g32p_row19_traceSegment_030_0720_0018, g32p_row19_traceSegment_030_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 756 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 765 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 756 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 756 9 9, g32p_row19_traceSegment_030_0756_0009, g32p_row19_traceSegment_030_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 783 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 774 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 774 9 9, g32p_row19_traceSegment_030_0774_0009, g32p_row19_traceSegment_030_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 756 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 756 18 18, g32p_row19_traceSegment_030_0756_0018, g32p_row19_traceSegment_030_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 720 72 = [0, 0, 0, 3, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 720 36 36, g32p_row19_traceSegment_030_0720_0036, g32p_row19_traceSegment_030_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 801 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 792 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 792 9 9, g32p_row19_traceSegment_030_0792_0009, g32p_row19_traceSegment_030_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 810 9 9, g32p_row19_traceSegment_030_0810_0009, g32p_row19_traceSegment_030_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 792 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 792 18 18, g32p_row19_traceSegment_030_0792_0018, g32p_row19_traceSegment_030_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 828 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 837 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 828 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 828 9 9, g32p_row19_traceSegment_030_0828_0009, g32p_row19_traceSegment_030_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 846 9 9, g32p_row19_traceSegment_030_0846_0009, g32p_row19_traceSegment_030_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 828 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 828 18 18, g32p_row19_traceSegment_030_0828_0018, g32p_row19_traceSegment_030_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 792 72 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 792 36 36, g32p_row19_traceSegment_030_0792_0036, g32p_row19_traceSegment_030_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 720 144 = [0, 0, 0, 5, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 720 72 72, g32p_row19_traceSegment_030_0720_0072, g32p_row19_traceSegment_030_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_030 576 288 = [0, 0, 0, 8, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 576 144 144, g32p_row19_traceSegment_030_0576_0144, g32p_row19_traceSegment_030_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 864 9 9, g32p_row19_traceSegment_030_0864_0009, g32p_row19_traceSegment_030_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 882 9 9, g32p_row19_traceSegment_030_0882_0009, g32p_row19_traceSegment_030_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 864 18 18, g32p_row19_traceSegment_030_0864_0018, g32p_row19_traceSegment_030_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 900 9 9, g32p_row19_traceSegment_030_0900_0009, g32p_row19_traceSegment_030_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 918 9 9, g32p_row19_traceSegment_030_0918_0009, g32p_row19_traceSegment_030_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 900 18 18, g32p_row19_traceSegment_030_0900_0018, g32p_row19_traceSegment_030_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 864 36 36, g32p_row19_traceSegment_030_0864_0036, g32p_row19_traceSegment_030_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 936 9 9, g32p_row19_traceSegment_030_0936_0009, g32p_row19_traceSegment_030_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 963 9 = [0, 0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 954 18 = [0, 0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 954 9 9, g32p_row19_traceSegment_030_0954_0009, g32p_row19_traceSegment_030_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 936 36 = [0, 0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 936 18 18, g32p_row19_traceSegment_030_0936_0018, g32p_row19_traceSegment_030_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 981 9 = [0, 0, 0, 2, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 972 18 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 972 9 9, g32p_row19_traceSegment_030_0972_0009, g32p_row19_traceSegment_030_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 990 9 9, g32p_row19_traceSegment_030_0990_0009, g32p_row19_traceSegment_030_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 972 36 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 972 18 18, g32p_row19_traceSegment_030_0972_0018, g32p_row19_traceSegment_030_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 936 72 = [0, 0, 0, 3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 936 36 36, g32p_row19_traceSegment_030_0936_0036, g32p_row19_traceSegment_030_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 864 144 = [0, 0, 0, 3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 864 72 72, g32p_row19_traceSegment_030_0864_0072, g32p_row19_traceSegment_030_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1008 9 9, g32p_row19_traceSegment_030_1008_0009, g32p_row19_traceSegment_030_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1026 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1035 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1026 18 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1026 9 9, g32p_row19_traceSegment_030_1026_0009, g32p_row19_traceSegment_030_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 1008 36 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1008 18 18, g32p_row19_traceSegment_030_1008_0018, g32p_row19_traceSegment_030_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1053 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1044 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1044 9 9, g32p_row19_traceSegment_030_1044_0009, g32p_row19_traceSegment_030_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1071 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1062 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1062 9 9, g32p_row19_traceSegment_030_1062_0009, g32p_row19_traceSegment_030_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 1044 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1044 18 18, g32p_row19_traceSegment_030_1044_0018, g32p_row19_traceSegment_030_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 1008 72 = [0, 0, 0, 1, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1008 36 36, g32p_row19_traceSegment_030_1008_0036, g32p_row19_traceSegment_030_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1080 9 9, g32p_row19_traceSegment_030_1080_0009, g32p_row19_traceSegment_030_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1098 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1098 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1098 9 9, g32p_row19_traceSegment_030_1098_0009, g32p_row19_traceSegment_030_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 1080 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1080 18 18, g32p_row19_traceSegment_030_1080_0018, g32p_row19_traceSegment_030_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1116 9 9, g32p_row19_traceSegment_030_1116_0009, g32p_row19_traceSegment_030_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_030 1143 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_030_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_030 1134 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1134 9 9, g32p_row19_traceSegment_030_1134_0009, g32p_row19_traceSegment_030_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_030 1116 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1116 18 18, g32p_row19_traceSegment_030_1116_0018, g32p_row19_traceSegment_030_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_030 1080 72 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1080 36 36, g32p_row19_traceSegment_030_1080_0036, g32p_row19_traceSegment_030_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_030_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_030 1008 144 = [0, 0, 0, 3, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 1008 72 72, g32p_row19_traceSegment_030_1008_0072, g32p_row19_traceSegment_030_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_030 864 288 = [0, 0, 0, 6, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 864 144 144, g32p_row19_traceSegment_030_0864_0144, g32p_row19_traceSegment_030_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_030 576 576 = [0, 0, 0, 14, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 576 288 288, g32p_row19_traceSegment_030_0576_0288, g32p_row19_traceSegment_030_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_030_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_030 0 1152 = [0, 0, 0, 32, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_030 0 576 576, g32p_row19_traceSegment_030_0000_0576, g32p_row19_traceSegment_030_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 30 = [0, 0, 0, 32, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_030_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_031 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 31 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_031_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 9 9, g32p_row19_traceSegment_031_0000_0009, g32p_row19_traceSegment_031_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 27 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 18 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 18 9 9, g32p_row19_traceSegment_031_0018_0009, g32p_row19_traceSegment_031_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 0 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 18 18, g32p_row19_traceSegment_031_0000_0018, g32p_row19_traceSegment_031_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 36 9 9, g32p_row19_traceSegment_031_0036_0009, g32p_row19_traceSegment_031_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 54 9 9, g32p_row19_traceSegment_031_0054_0009, g32p_row19_traceSegment_031_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 36 18 18, g32p_row19_traceSegment_031_0036_0018, g32p_row19_traceSegment_031_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 0 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 36 36, g32p_row19_traceSegment_031_0000_0036, g32p_row19_traceSegment_031_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 72 9 9, g32p_row19_traceSegment_031_0072_0009, g32p_row19_traceSegment_031_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 90 9 9, g32p_row19_traceSegment_031_0090_0009, g32p_row19_traceSegment_031_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 72 18 18, g32p_row19_traceSegment_031_0072_0018, g32p_row19_traceSegment_031_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 108 9 9, g32p_row19_traceSegment_031_0108_0009, g32p_row19_traceSegment_031_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 126 9 9, g32p_row19_traceSegment_031_0126_0009, g32p_row19_traceSegment_031_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 108 18 18, g32p_row19_traceSegment_031_0108_0018, g32p_row19_traceSegment_031_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 72 36 36, g32p_row19_traceSegment_031_0072_0036, g32p_row19_traceSegment_031_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 72 72, g32p_row19_traceSegment_031_0000_0072, g32p_row19_traceSegment_031_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 144 9 9, g32p_row19_traceSegment_031_0144_0009, g32p_row19_traceSegment_031_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 162 9 9, g32p_row19_traceSegment_031_0162_0009, g32p_row19_traceSegment_031_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 144 18 18, g32p_row19_traceSegment_031_0144_0018, g32p_row19_traceSegment_031_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 180 9 9, g32p_row19_traceSegment_031_0180_0009, g32p_row19_traceSegment_031_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 198 9 9, g32p_row19_traceSegment_031_0198_0009, g32p_row19_traceSegment_031_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 180 18 18, g32p_row19_traceSegment_031_0180_0018, g32p_row19_traceSegment_031_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 144 36 36, g32p_row19_traceSegment_031_0144_0036, g32p_row19_traceSegment_031_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 216 9 9, g32p_row19_traceSegment_031_0216_0009, g32p_row19_traceSegment_031_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 234 9 9, g32p_row19_traceSegment_031_0234_0009, g32p_row19_traceSegment_031_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 216 18 18, g32p_row19_traceSegment_031_0216_0018, g32p_row19_traceSegment_031_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 261 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 252 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 252 9 9, g32p_row19_traceSegment_031_0252_0009, g32p_row19_traceSegment_031_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 270 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 270 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 270 9 9, g32p_row19_traceSegment_031_0270_0009, g32p_row19_traceSegment_031_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 252 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 252 18 18, g32p_row19_traceSegment_031_0252_0018, g32p_row19_traceSegment_031_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 216 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 216 36 36, g32p_row19_traceSegment_031_0216_0036, g32p_row19_traceSegment_031_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 144 72 72, g32p_row19_traceSegment_031_0144_0072, g32p_row19_traceSegment_031_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_031 0 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 144 144, g32p_row19_traceSegment_031_0000_0144, g32p_row19_traceSegment_031_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 288 9 9, g32p_row19_traceSegment_031_0288_0009, g32p_row19_traceSegment_031_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 306 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 315 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 306 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 306 9 9, g32p_row19_traceSegment_031_0306_0009, g32p_row19_traceSegment_031_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 288 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 288 18 18, g32p_row19_traceSegment_031_0288_0018, g32p_row19_traceSegment_031_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 324 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 324 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 324 9 9, g32p_row19_traceSegment_031_0324_0009, g32p_row19_traceSegment_031_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 342 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 351 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 342 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 342 9 9, g32p_row19_traceSegment_031_0342_0009, g32p_row19_traceSegment_031_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 324 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 324 18 18, g32p_row19_traceSegment_031_0324_0018, g32p_row19_traceSegment_031_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 288 72 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 288 36 36, g32p_row19_traceSegment_031_0288_0036, g32p_row19_traceSegment_031_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 360 9 9, g32p_row19_traceSegment_031_0360_0009, g32p_row19_traceSegment_031_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 378 9 9, g32p_row19_traceSegment_031_0378_0009, g32p_row19_traceSegment_031_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 360 18 18, g32p_row19_traceSegment_031_0360_0018, g32p_row19_traceSegment_031_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 396 9 9, g32p_row19_traceSegment_031_0396_0009, g32p_row19_traceSegment_031_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 414 9 9, g32p_row19_traceSegment_031_0414_0009, g32p_row19_traceSegment_031_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 396 18 18, g32p_row19_traceSegment_031_0396_0018, g32p_row19_traceSegment_031_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 360 36 36, g32p_row19_traceSegment_031_0360_0036, g32p_row19_traceSegment_031_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 288 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 288 72 72, g32p_row19_traceSegment_031_0288_0072, g32p_row19_traceSegment_031_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 432 9 9, g32p_row19_traceSegment_031_0432_0009, g32p_row19_traceSegment_031_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 450 9 9, g32p_row19_traceSegment_031_0450_0009, g32p_row19_traceSegment_031_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 432 18 18, g32p_row19_traceSegment_031_0432_0018, g32p_row19_traceSegment_031_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 468 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 468 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 468 9 9, g32p_row19_traceSegment_031_0468_0009, g32p_row19_traceSegment_031_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 486 9 9, g32p_row19_traceSegment_031_0486_0009, g32p_row19_traceSegment_031_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 468 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 468 18 18, g32p_row19_traceSegment_031_0468_0018, g32p_row19_traceSegment_031_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 432 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 432 36 36, g32p_row19_traceSegment_031_0432_0036, g32p_row19_traceSegment_031_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 504 9 9, g32p_row19_traceSegment_031_0504_0009, g32p_row19_traceSegment_031_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 522 9 9, g32p_row19_traceSegment_031_0522_0009, g32p_row19_traceSegment_031_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 504 18 18, g32p_row19_traceSegment_031_0504_0018, g32p_row19_traceSegment_031_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 540 9 9, g32p_row19_traceSegment_031_0540_0009, g32p_row19_traceSegment_031_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 558 9 9, g32p_row19_traceSegment_031_0558_0009, g32p_row19_traceSegment_031_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 540 18 18, g32p_row19_traceSegment_031_0540_0018, g32p_row19_traceSegment_031_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 504 36 36, g32p_row19_traceSegment_031_0504_0036, g32p_row19_traceSegment_031_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 432 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 432 72 72, g32p_row19_traceSegment_031_0432_0072, g32p_row19_traceSegment_031_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_031 288 288 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 288 144 144, g32p_row19_traceSegment_031_0288_0144, g32p_row19_traceSegment_031_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_031 0 576 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 288 288, g32p_row19_traceSegment_031_0000_0288, g32p_row19_traceSegment_031_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 576 9 9, g32p_row19_traceSegment_031_0576_0009, g32p_row19_traceSegment_031_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 594 9 9, g32p_row19_traceSegment_031_0594_0009, g32p_row19_traceSegment_031_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 576 18 18, g32p_row19_traceSegment_031_0576_0018, g32p_row19_traceSegment_031_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 612 9 9, g32p_row19_traceSegment_031_0612_0009, g32p_row19_traceSegment_031_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 630 9 9, g32p_row19_traceSegment_031_0630_0009, g32p_row19_traceSegment_031_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 612 18 18, g32p_row19_traceSegment_031_0612_0018, g32p_row19_traceSegment_031_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 576 36 36, g32p_row19_traceSegment_031_0576_0036, g32p_row19_traceSegment_031_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 648 9 9, g32p_row19_traceSegment_031_0648_0009, g32p_row19_traceSegment_031_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 666 9 9, g32p_row19_traceSegment_031_0666_0009, g32p_row19_traceSegment_031_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 648 18 18, g32p_row19_traceSegment_031_0648_0018, g32p_row19_traceSegment_031_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 684 9 9, g32p_row19_traceSegment_031_0684_0009, g32p_row19_traceSegment_031_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 702 9 9, g32p_row19_traceSegment_031_0702_0009, g32p_row19_traceSegment_031_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 684 18 18, g32p_row19_traceSegment_031_0684_0018, g32p_row19_traceSegment_031_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 648 36 36, g32p_row19_traceSegment_031_0648_0036, g32p_row19_traceSegment_031_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 576 72 72, g32p_row19_traceSegment_031_0576_0072, g32p_row19_traceSegment_031_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 720 9 9, g32p_row19_traceSegment_031_0720_0009, g32p_row19_traceSegment_031_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 738 9 9, g32p_row19_traceSegment_031_0738_0009, g32p_row19_traceSegment_031_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 720 18 18, g32p_row19_traceSegment_031_0720_0018, g32p_row19_traceSegment_031_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 756 9 9, g32p_row19_traceSegment_031_0756_0009, g32p_row19_traceSegment_031_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 774 9 9, g32p_row19_traceSegment_031_0774_0009, g32p_row19_traceSegment_031_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 756 18 18, g32p_row19_traceSegment_031_0756_0018, g32p_row19_traceSegment_031_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 720 36 36, g32p_row19_traceSegment_031_0720_0036, g32p_row19_traceSegment_031_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 792 9 9, g32p_row19_traceSegment_031_0792_0009, g32p_row19_traceSegment_031_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 810 9 9, g32p_row19_traceSegment_031_0810_0009, g32p_row19_traceSegment_031_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 792 18 18, g32p_row19_traceSegment_031_0792_0018, g32p_row19_traceSegment_031_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 828 9 9, g32p_row19_traceSegment_031_0828_0009, g32p_row19_traceSegment_031_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 846 9 9, g32p_row19_traceSegment_031_0846_0009, g32p_row19_traceSegment_031_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 828 18 18, g32p_row19_traceSegment_031_0828_0018, g32p_row19_traceSegment_031_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 792 36 36, g32p_row19_traceSegment_031_0792_0036, g32p_row19_traceSegment_031_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 720 72 72, g32p_row19_traceSegment_031_0720_0072, g32p_row19_traceSegment_031_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_031 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 576 144 144, g32p_row19_traceSegment_031_0576_0144, g32p_row19_traceSegment_031_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 873 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 864 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 864 9 9, g32p_row19_traceSegment_031_0864_0009, g32p_row19_traceSegment_031_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 882 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 882 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 882 9 9, g32p_row19_traceSegment_031_0882_0009, g32p_row19_traceSegment_031_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 864 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 864 18 18, g32p_row19_traceSegment_031_0864_0018, g32p_row19_traceSegment_031_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 900 9 9, g32p_row19_traceSegment_031_0900_0009, g32p_row19_traceSegment_031_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 918 9 9, g32p_row19_traceSegment_031_0918_0009, g32p_row19_traceSegment_031_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 900 18 18, g32p_row19_traceSegment_031_0900_0018, g32p_row19_traceSegment_031_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 864 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 864 36 36, g32p_row19_traceSegment_031_0864_0036, g32p_row19_traceSegment_031_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 936 9 9, g32p_row19_traceSegment_031_0936_0009, g32p_row19_traceSegment_031_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 954 9 9, g32p_row19_traceSegment_031_0954_0009, g32p_row19_traceSegment_031_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 936 18 18, g32p_row19_traceSegment_031_0936_0018, g32p_row19_traceSegment_031_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 972 9 9, g32p_row19_traceSegment_031_0972_0009, g32p_row19_traceSegment_031_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 990 9 9, g32p_row19_traceSegment_031_0990_0009, g32p_row19_traceSegment_031_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 972 18 18, g32p_row19_traceSegment_031_0972_0018, g32p_row19_traceSegment_031_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 936 36 36, g32p_row19_traceSegment_031_0936_0036, g32p_row19_traceSegment_031_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 864 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 864 72 72, g32p_row19_traceSegment_031_0864_0072, g32p_row19_traceSegment_031_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1008 9 9, g32p_row19_traceSegment_031_1008_0009, g32p_row19_traceSegment_031_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1026 9 9, g32p_row19_traceSegment_031_1026_0009, g32p_row19_traceSegment_031_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1008 18 18, g32p_row19_traceSegment_031_1008_0018, g32p_row19_traceSegment_031_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1044 9 9, g32p_row19_traceSegment_031_1044_0009, g32p_row19_traceSegment_031_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1062 9 9, g32p_row19_traceSegment_031_1062_0009, g32p_row19_traceSegment_031_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1044 18 18, g32p_row19_traceSegment_031_1044_0018, g32p_row19_traceSegment_031_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1008 36 36, g32p_row19_traceSegment_031_1008_0036, g32p_row19_traceSegment_031_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1080 9 9, g32p_row19_traceSegment_031_1080_0009, g32p_row19_traceSegment_031_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1098 9 9, g32p_row19_traceSegment_031_1098_0009, g32p_row19_traceSegment_031_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1080 18 18, g32p_row19_traceSegment_031_1080_0018, g32p_row19_traceSegment_031_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1116 9 9, g32p_row19_traceSegment_031_1116_0009, g32p_row19_traceSegment_031_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_031 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_031_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_031 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1134 9 9, g32p_row19_traceSegment_031_1134_0009, g32p_row19_traceSegment_031_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_031 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1116 18 18, g32p_row19_traceSegment_031_1116_0018, g32p_row19_traceSegment_031_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_031 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1080 36 36, g32p_row19_traceSegment_031_1080_0036, g32p_row19_traceSegment_031_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_031_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_031 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 1008 72 72, g32p_row19_traceSegment_031_1008_0072, g32p_row19_traceSegment_031_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_031 864 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 864 144 144, g32p_row19_traceSegment_031_0864_0144, g32p_row19_traceSegment_031_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_031 576 576 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 576 288 288, g32p_row19_traceSegment_031_0576_0288, g32p_row19_traceSegment_031_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_031_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_031 0 1152 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_031 0 576 576, g32p_row19_traceSegment_031_0000_0576, g32p_row19_traceSegment_031_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 31 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_031_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_034_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 9 9, g32p_row19_traceSegment_034_0000_0009, g32p_row19_traceSegment_034_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 18 9 9, g32p_row19_traceSegment_034_0018_0009, g32p_row19_traceSegment_034_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 18 18, g32p_row19_traceSegment_034_0000_0018, g32p_row19_traceSegment_034_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 36 9 9, g32p_row19_traceSegment_034_0036_0009, g32p_row19_traceSegment_034_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 54 9 9, g32p_row19_traceSegment_034_0054_0009, g32p_row19_traceSegment_034_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 36 18 18, g32p_row19_traceSegment_034_0036_0018, g32p_row19_traceSegment_034_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 36 36, g32p_row19_traceSegment_034_0000_0036, g32p_row19_traceSegment_034_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 72 9 9, g32p_row19_traceSegment_034_0072_0009, g32p_row19_traceSegment_034_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 99 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 90 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 90 9 9, g32p_row19_traceSegment_034_0090_0009, g32p_row19_traceSegment_034_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 72 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 72 18 18, g32p_row19_traceSegment_034_0072_0018, g32p_row19_traceSegment_034_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 108 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 108 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 108 9 9, g32p_row19_traceSegment_034_0108_0009, g32p_row19_traceSegment_034_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 135 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 126 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 126 9 9, g32p_row19_traceSegment_034_0126_0009, g32p_row19_traceSegment_034_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 108 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 108 18 18, g32p_row19_traceSegment_034_0108_0018, g32p_row19_traceSegment_034_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 72 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 72 36 36, g32p_row19_traceSegment_034_0072_0036, g32p_row19_traceSegment_034_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 0 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 72 72, g32p_row19_traceSegment_034_0000_0072, g32p_row19_traceSegment_034_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 144 9 9, g32p_row19_traceSegment_034_0144_0009, g32p_row19_traceSegment_034_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 162 9 9, g32p_row19_traceSegment_034_0162_0009, g32p_row19_traceSegment_034_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 144 18 18, g32p_row19_traceSegment_034_0144_0018, g32p_row19_traceSegment_034_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 180 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 180 9 9, g32p_row19_traceSegment_034_0180_0009, g32p_row19_traceSegment_034_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 198 9 9, g32p_row19_traceSegment_034_0198_0009, g32p_row19_traceSegment_034_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 180 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 180 18 18, g32p_row19_traceSegment_034_0180_0018, g32p_row19_traceSegment_034_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 144 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 144 36 36, g32p_row19_traceSegment_034_0144_0036, g32p_row19_traceSegment_034_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 216 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 225 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 216 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 216 9 9, g32p_row19_traceSegment_034_0216_0009, g32p_row19_traceSegment_034_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 234 9 9, g32p_row19_traceSegment_034_0234_0009, g32p_row19_traceSegment_034_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 216 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 216 18 18, g32p_row19_traceSegment_034_0216_0018, g32p_row19_traceSegment_034_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 252 9 9, g32p_row19_traceSegment_034_0252_0009, g32p_row19_traceSegment_034_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 270 9 9, g32p_row19_traceSegment_034_0270_0009, g32p_row19_traceSegment_034_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 252 18 18, g32p_row19_traceSegment_034_0252_0018, g32p_row19_traceSegment_034_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 216 72 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 216 36 36, g32p_row19_traceSegment_034_0216_0036, g32p_row19_traceSegment_034_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 144 144 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 144 72 72, g32p_row19_traceSegment_034_0144_0072, g32p_row19_traceSegment_034_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_034 0 288 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 144 144, g32p_row19_traceSegment_034_0000_0144, g32p_row19_traceSegment_034_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 288 9 9, g32p_row19_traceSegment_034_0288_0009, g32p_row19_traceSegment_034_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 306 9 9, g32p_row19_traceSegment_034_0306_0009, g32p_row19_traceSegment_034_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 288 18 18, g32p_row19_traceSegment_034_0288_0018, g32p_row19_traceSegment_034_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 324 9 9, g32p_row19_traceSegment_034_0324_0009, g32p_row19_traceSegment_034_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 342 9 9, g32p_row19_traceSegment_034_0342_0009, g32p_row19_traceSegment_034_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 324 18 18, g32p_row19_traceSegment_034_0324_0018, g32p_row19_traceSegment_034_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 288 36 36, g32p_row19_traceSegment_034_0288_0036, g32p_row19_traceSegment_034_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 360 9 9, g32p_row19_traceSegment_034_0360_0009, g32p_row19_traceSegment_034_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 378 9 9, g32p_row19_traceSegment_034_0378_0009, g32p_row19_traceSegment_034_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 360 18 18, g32p_row19_traceSegment_034_0360_0018, g32p_row19_traceSegment_034_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 396 9 9, g32p_row19_traceSegment_034_0396_0009, g32p_row19_traceSegment_034_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 414 9 9, g32p_row19_traceSegment_034_0414_0009, g32p_row19_traceSegment_034_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 396 18 18, g32p_row19_traceSegment_034_0396_0018, g32p_row19_traceSegment_034_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 360 36 36, g32p_row19_traceSegment_034_0360_0036, g32p_row19_traceSegment_034_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 288 72 72, g32p_row19_traceSegment_034_0288_0072, g32p_row19_traceSegment_034_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 432 9 9, g32p_row19_traceSegment_034_0432_0009, g32p_row19_traceSegment_034_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 450 9 9, g32p_row19_traceSegment_034_0450_0009, g32p_row19_traceSegment_034_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 432 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 432 18 18, g32p_row19_traceSegment_034_0432_0018, g32p_row19_traceSegment_034_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 468 9 9, g32p_row19_traceSegment_034_0468_0009, g32p_row19_traceSegment_034_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 486 9 9, g32p_row19_traceSegment_034_0486_0009, g32p_row19_traceSegment_034_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 468 18 18, g32p_row19_traceSegment_034_0468_0018, g32p_row19_traceSegment_034_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 432 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 432 36 36, g32p_row19_traceSegment_034_0432_0036, g32p_row19_traceSegment_034_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 504 9 9, g32p_row19_traceSegment_034_0504_0009, g32p_row19_traceSegment_034_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 522 9 9, g32p_row19_traceSegment_034_0522_0009, g32p_row19_traceSegment_034_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 504 18 18, g32p_row19_traceSegment_034_0504_0018, g32p_row19_traceSegment_034_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 540 9 9, g32p_row19_traceSegment_034_0540_0009, g32p_row19_traceSegment_034_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 558 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 558 9 9, g32p_row19_traceSegment_034_0558_0009, g32p_row19_traceSegment_034_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 540 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 540 18 18, g32p_row19_traceSegment_034_0540_0018, g32p_row19_traceSegment_034_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 504 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 504 36 36, g32p_row19_traceSegment_034_0504_0036, g32p_row19_traceSegment_034_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 432 144 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 432 72 72, g32p_row19_traceSegment_034_0432_0072, g32p_row19_traceSegment_034_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_034 288 288 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 288 144 144, g32p_row19_traceSegment_034_0288_0144, g32p_row19_traceSegment_034_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_034 0 576 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 288 288, g32p_row19_traceSegment_034_0000_0288, g32p_row19_traceSegment_034_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 576 9 9, g32p_row19_traceSegment_034_0576_0009, g32p_row19_traceSegment_034_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 594 9 9, g32p_row19_traceSegment_034_0594_0009, g32p_row19_traceSegment_034_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 576 18 18, g32p_row19_traceSegment_034_0576_0018, g32p_row19_traceSegment_034_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 612 9 9, g32p_row19_traceSegment_034_0612_0009, g32p_row19_traceSegment_034_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 630 9 9, g32p_row19_traceSegment_034_0630_0009, g32p_row19_traceSegment_034_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 612 18 18, g32p_row19_traceSegment_034_0612_0018, g32p_row19_traceSegment_034_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 576 36 36, g32p_row19_traceSegment_034_0576_0036, g32p_row19_traceSegment_034_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 648 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 648 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 648 9 9, g32p_row19_traceSegment_034_0648_0009, g32p_row19_traceSegment_034_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 666 9 9, g32p_row19_traceSegment_034_0666_0009, g32p_row19_traceSegment_034_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 648 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 648 18 18, g32p_row19_traceSegment_034_0648_0018, g32p_row19_traceSegment_034_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 684 9 9, g32p_row19_traceSegment_034_0684_0009, g32p_row19_traceSegment_034_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 711 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 702 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 702 9 9, g32p_row19_traceSegment_034_0702_0009, g32p_row19_traceSegment_034_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 684 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 684 18 18, g32p_row19_traceSegment_034_0684_0018, g32p_row19_traceSegment_034_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 648 72 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 648 36 36, g32p_row19_traceSegment_034_0648_0036, g32p_row19_traceSegment_034_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 576 144 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 576 72 72, g32p_row19_traceSegment_034_0576_0072, g32p_row19_traceSegment_034_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 720 9 9, g32p_row19_traceSegment_034_0720_0009, g32p_row19_traceSegment_034_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 738 9 9, g32p_row19_traceSegment_034_0738_0009, g32p_row19_traceSegment_034_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 720 18 18, g32p_row19_traceSegment_034_0720_0018, g32p_row19_traceSegment_034_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 756 9 9, g32p_row19_traceSegment_034_0756_0009, g32p_row19_traceSegment_034_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 774 9 9, g32p_row19_traceSegment_034_0774_0009, g32p_row19_traceSegment_034_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 756 18 18, g32p_row19_traceSegment_034_0756_0018, g32p_row19_traceSegment_034_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 720 36 36, g32p_row19_traceSegment_034_0720_0036, g32p_row19_traceSegment_034_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 792 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 792 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 792 9 9, g32p_row19_traceSegment_034_0792_0009, g32p_row19_traceSegment_034_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 810 9 9, g32p_row19_traceSegment_034_0810_0009, g32p_row19_traceSegment_034_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 792 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 792 18 18, g32p_row19_traceSegment_034_0792_0018, g32p_row19_traceSegment_034_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 828 9 9, g32p_row19_traceSegment_034_0828_0009, g32p_row19_traceSegment_034_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 855 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 846 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 846 9 9, g32p_row19_traceSegment_034_0846_0009, g32p_row19_traceSegment_034_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 828 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 828 18 18, g32p_row19_traceSegment_034_0828_0018, g32p_row19_traceSegment_034_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 792 72 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 792 36 36, g32p_row19_traceSegment_034_0792_0036, g32p_row19_traceSegment_034_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 720 144 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 720 72 72, g32p_row19_traceSegment_034_0720_0072, g32p_row19_traceSegment_034_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_034 576 288 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 576 144 144, g32p_row19_traceSegment_034_0576_0144, g32p_row19_traceSegment_034_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 873 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 864 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 864 9 9, g32p_row19_traceSegment_034_0864_0009, g32p_row19_traceSegment_034_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 882 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 891 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 882 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 882 9 9, g32p_row19_traceSegment_034_0882_0009, g32p_row19_traceSegment_034_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 864 36 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 864 18 18, g32p_row19_traceSegment_034_0864_0018, g32p_row19_traceSegment_034_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 909 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 900 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 900 9 9, g32p_row19_traceSegment_034_0900_0009, g32p_row19_traceSegment_034_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 918 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 927 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 918 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 918 9 9, g32p_row19_traceSegment_034_0918_0009, g32p_row19_traceSegment_034_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 900 36 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 900 18 18, g32p_row19_traceSegment_034_0900_0018, g32p_row19_traceSegment_034_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 864 72 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 864 36 36, g32p_row19_traceSegment_034_0864_0036, g32p_row19_traceSegment_034_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 936 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 936 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 936 9 9, g32p_row19_traceSegment_034_0936_0009, g32p_row19_traceSegment_034_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 954 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 954 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 954 9 9, g32p_row19_traceSegment_034_0954_0009, g32p_row19_traceSegment_034_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 936 36 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 936 18 18, g32p_row19_traceSegment_034_0936_0018, g32p_row19_traceSegment_034_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 972 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 981 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 972 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 972 9 9, g32p_row19_traceSegment_034_0972_0009, g32p_row19_traceSegment_034_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 990 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 999 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 990 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 990 9 9, g32p_row19_traceSegment_034_0990_0009, g32p_row19_traceSegment_034_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 972 36 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 972 18 18, g32p_row19_traceSegment_034_0972_0018, g32p_row19_traceSegment_034_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 936 72 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 936 36 36, g32p_row19_traceSegment_034_0936_0036, g32p_row19_traceSegment_034_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 864 144 = [0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 864 72 72, g32p_row19_traceSegment_034_0864_0072, g32p_row19_traceSegment_034_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1008 9 9, g32p_row19_traceSegment_034_1008_0009, g32p_row19_traceSegment_034_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1026 9 9, g32p_row19_traceSegment_034_1026_0009, g32p_row19_traceSegment_034_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1008 18 18, g32p_row19_traceSegment_034_1008_0018, g32p_row19_traceSegment_034_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1044 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1053 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1044 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1044 9 9, g32p_row19_traceSegment_034_1044_0009, g32p_row19_traceSegment_034_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1062 9 9, g32p_row19_traceSegment_034_1062_0009, g32p_row19_traceSegment_034_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 1044 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1044 18 18, g32p_row19_traceSegment_034_1044_0018, g32p_row19_traceSegment_034_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 1008 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1008 36 36, g32p_row19_traceSegment_034_1008_0036, g32p_row19_traceSegment_034_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1080 9 9, g32p_row19_traceSegment_034_1080_0009, g32p_row19_traceSegment_034_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1098 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1107 9 = [0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1098 18 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1098 9 9, g32p_row19_traceSegment_034_1098_0009, g32p_row19_traceSegment_034_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 1080 36 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1080 18 18, g32p_row19_traceSegment_034_1080_0018, g32p_row19_traceSegment_034_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1125 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1116 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1116 9 9, g32p_row19_traceSegment_034_1116_0009, g32p_row19_traceSegment_034_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_034 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_034_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_034 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1134 9 9, g32p_row19_traceSegment_034_1134_0009, g32p_row19_traceSegment_034_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_034 1116 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1116 18 18, g32p_row19_traceSegment_034_1116_0018, g32p_row19_traceSegment_034_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_034 1080 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1080 36 36, g32p_row19_traceSegment_034_1080_0036, g32p_row19_traceSegment_034_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_034_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_034 1008 144 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 1008 72 72, g32p_row19_traceSegment_034_1008_0072, g32p_row19_traceSegment_034_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_034 864 288 = [0, 0, 0, 0, 31] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 864 144 144, g32p_row19_traceSegment_034_0864_0144, g32p_row19_traceSegment_034_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_034 576 576 = [0, 2, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 576 288 288, g32p_row19_traceSegment_034_0576_0288, g32p_row19_traceSegment_034_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_034_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_034 0 1152 = [0, 8, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_034 0 576 576, g32p_row19_traceSegment_034_0000_0576, g32p_row19_traceSegment_034_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 34 = [0, 8, 0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_034_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_037_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 9 9, g32p_row19_traceSegment_037_0000_0009, g32p_row19_traceSegment_037_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 18 9 9, g32p_row19_traceSegment_037_0018_0009, g32p_row19_traceSegment_037_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 18 18, g32p_row19_traceSegment_037_0000_0018, g32p_row19_traceSegment_037_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 36 9 9, g32p_row19_traceSegment_037_0036_0009, g32p_row19_traceSegment_037_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 54 9 9, g32p_row19_traceSegment_037_0054_0009, g32p_row19_traceSegment_037_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 36 18 18, g32p_row19_traceSegment_037_0036_0018, g32p_row19_traceSegment_037_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 36 36, g32p_row19_traceSegment_037_0000_0036, g32p_row19_traceSegment_037_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 72 9 9, g32p_row19_traceSegment_037_0072_0009, g32p_row19_traceSegment_037_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 90 9 9, g32p_row19_traceSegment_037_0090_0009, g32p_row19_traceSegment_037_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 72 18 18, g32p_row19_traceSegment_037_0072_0018, g32p_row19_traceSegment_037_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 108 9 9, g32p_row19_traceSegment_037_0108_0009, g32p_row19_traceSegment_037_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 126 9 9, g32p_row19_traceSegment_037_0126_0009, g32p_row19_traceSegment_037_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 108 18 18, g32p_row19_traceSegment_037_0108_0018, g32p_row19_traceSegment_037_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 72 36 36, g32p_row19_traceSegment_037_0072_0036, g32p_row19_traceSegment_037_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 72 72, g32p_row19_traceSegment_037_0000_0072, g32p_row19_traceSegment_037_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 153 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 144 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 144 9 9, g32p_row19_traceSegment_037_0144_0009, g32p_row19_traceSegment_037_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 162 9 9, g32p_row19_traceSegment_037_0162_0009, g32p_row19_traceSegment_037_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 144 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 144 18 18, g32p_row19_traceSegment_037_0144_0018, g32p_row19_traceSegment_037_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 180 9 9, g32p_row19_traceSegment_037_0180_0009, g32p_row19_traceSegment_037_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 198 9 9, g32p_row19_traceSegment_037_0198_0009, g32p_row19_traceSegment_037_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 180 18 18, g32p_row19_traceSegment_037_0180_0018, g32p_row19_traceSegment_037_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 144 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 144 36 36, g32p_row19_traceSegment_037_0144_0036, g32p_row19_traceSegment_037_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 216 9 9, g32p_row19_traceSegment_037_0216_0009, g32p_row19_traceSegment_037_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 234 9 9, g32p_row19_traceSegment_037_0234_0009, g32p_row19_traceSegment_037_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 216 18 18, g32p_row19_traceSegment_037_0216_0018, g32p_row19_traceSegment_037_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 252 9 9, g32p_row19_traceSegment_037_0252_0009, g32p_row19_traceSegment_037_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 270 9 9, g32p_row19_traceSegment_037_0270_0009, g32p_row19_traceSegment_037_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 252 18 18, g32p_row19_traceSegment_037_0252_0018, g32p_row19_traceSegment_037_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 216 36 36, g32p_row19_traceSegment_037_0216_0036, g32p_row19_traceSegment_037_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 144 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 144 72 72, g32p_row19_traceSegment_037_0144_0072, g32p_row19_traceSegment_037_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_037 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 144 144, g32p_row19_traceSegment_037_0000_0144, g32p_row19_traceSegment_037_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 288 9 9, g32p_row19_traceSegment_037_0288_0009, g32p_row19_traceSegment_037_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 306 9 9, g32p_row19_traceSegment_037_0306_0009, g32p_row19_traceSegment_037_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 288 18 18, g32p_row19_traceSegment_037_0288_0018, g32p_row19_traceSegment_037_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 324 9 9, g32p_row19_traceSegment_037_0324_0009, g32p_row19_traceSegment_037_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 342 9 9, g32p_row19_traceSegment_037_0342_0009, g32p_row19_traceSegment_037_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 324 18 18, g32p_row19_traceSegment_037_0324_0018, g32p_row19_traceSegment_037_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 288 36 36, g32p_row19_traceSegment_037_0288_0036, g32p_row19_traceSegment_037_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 360 9 9, g32p_row19_traceSegment_037_0360_0009, g32p_row19_traceSegment_037_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 378 9 9, g32p_row19_traceSegment_037_0378_0009, g32p_row19_traceSegment_037_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 360 18 18, g32p_row19_traceSegment_037_0360_0018, g32p_row19_traceSegment_037_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 396 9 9, g32p_row19_traceSegment_037_0396_0009, g32p_row19_traceSegment_037_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 414 9 9, g32p_row19_traceSegment_037_0414_0009, g32p_row19_traceSegment_037_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 396 18 18, g32p_row19_traceSegment_037_0396_0018, g32p_row19_traceSegment_037_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 360 36 36, g32p_row19_traceSegment_037_0360_0036, g32p_row19_traceSegment_037_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 288 72 72, g32p_row19_traceSegment_037_0288_0072, g32p_row19_traceSegment_037_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 432 9 9, g32p_row19_traceSegment_037_0432_0009, g32p_row19_traceSegment_037_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 450 9 9, g32p_row19_traceSegment_037_0450_0009, g32p_row19_traceSegment_037_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 432 18 18, g32p_row19_traceSegment_037_0432_0018, g32p_row19_traceSegment_037_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 468 9 9, g32p_row19_traceSegment_037_0468_0009, g32p_row19_traceSegment_037_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 486 9 9, g32p_row19_traceSegment_037_0486_0009, g32p_row19_traceSegment_037_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 468 18 18, g32p_row19_traceSegment_037_0468_0018, g32p_row19_traceSegment_037_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 432 36 36, g32p_row19_traceSegment_037_0432_0036, g32p_row19_traceSegment_037_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 504 9 9, g32p_row19_traceSegment_037_0504_0009, g32p_row19_traceSegment_037_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 522 9 9, g32p_row19_traceSegment_037_0522_0009, g32p_row19_traceSegment_037_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 504 18 18, g32p_row19_traceSegment_037_0504_0018, g32p_row19_traceSegment_037_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 540 9 9, g32p_row19_traceSegment_037_0540_0009, g32p_row19_traceSegment_037_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 558 9 9, g32p_row19_traceSegment_037_0558_0009, g32p_row19_traceSegment_037_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 540 18 18, g32p_row19_traceSegment_037_0540_0018, g32p_row19_traceSegment_037_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 504 36 36, g32p_row19_traceSegment_037_0504_0036, g32p_row19_traceSegment_037_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 432 72 72, g32p_row19_traceSegment_037_0432_0072, g32p_row19_traceSegment_037_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_037 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 288 144 144, g32p_row19_traceSegment_037_0288_0144, g32p_row19_traceSegment_037_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_037 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 288 288, g32p_row19_traceSegment_037_0000_0288, g32p_row19_traceSegment_037_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 576 9 9, g32p_row19_traceSegment_037_0576_0009, g32p_row19_traceSegment_037_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 594 9 9, g32p_row19_traceSegment_037_0594_0009, g32p_row19_traceSegment_037_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 576 18 18, g32p_row19_traceSegment_037_0576_0018, g32p_row19_traceSegment_037_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 612 9 9, g32p_row19_traceSegment_037_0612_0009, g32p_row19_traceSegment_037_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 630 9 9, g32p_row19_traceSegment_037_0630_0009, g32p_row19_traceSegment_037_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 612 18 18, g32p_row19_traceSegment_037_0612_0018, g32p_row19_traceSegment_037_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 576 36 36, g32p_row19_traceSegment_037_0576_0036, g32p_row19_traceSegment_037_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 648 9 9, g32p_row19_traceSegment_037_0648_0009, g32p_row19_traceSegment_037_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 666 9 9, g32p_row19_traceSegment_037_0666_0009, g32p_row19_traceSegment_037_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 648 18 18, g32p_row19_traceSegment_037_0648_0018, g32p_row19_traceSegment_037_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 684 9 9, g32p_row19_traceSegment_037_0684_0009, g32p_row19_traceSegment_037_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 702 9 9, g32p_row19_traceSegment_037_0702_0009, g32p_row19_traceSegment_037_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 684 18 18, g32p_row19_traceSegment_037_0684_0018, g32p_row19_traceSegment_037_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 648 36 36, g32p_row19_traceSegment_037_0648_0036, g32p_row19_traceSegment_037_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 576 72 72, g32p_row19_traceSegment_037_0576_0072, g32p_row19_traceSegment_037_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 720 9 9, g32p_row19_traceSegment_037_0720_0009, g32p_row19_traceSegment_037_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 738 9 9, g32p_row19_traceSegment_037_0738_0009, g32p_row19_traceSegment_037_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 720 18 18, g32p_row19_traceSegment_037_0720_0018, g32p_row19_traceSegment_037_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 756 9 9, g32p_row19_traceSegment_037_0756_0009, g32p_row19_traceSegment_037_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 774 9 9, g32p_row19_traceSegment_037_0774_0009, g32p_row19_traceSegment_037_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 756 18 18, g32p_row19_traceSegment_037_0756_0018, g32p_row19_traceSegment_037_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 720 36 36, g32p_row19_traceSegment_037_0720_0036, g32p_row19_traceSegment_037_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 792 9 9, g32p_row19_traceSegment_037_0792_0009, g32p_row19_traceSegment_037_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 810 9 9, g32p_row19_traceSegment_037_0810_0009, g32p_row19_traceSegment_037_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 792 18 18, g32p_row19_traceSegment_037_0792_0018, g32p_row19_traceSegment_037_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 828 9 9, g32p_row19_traceSegment_037_0828_0009, g32p_row19_traceSegment_037_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 846 9 9, g32p_row19_traceSegment_037_0846_0009, g32p_row19_traceSegment_037_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 828 18 18, g32p_row19_traceSegment_037_0828_0018, g32p_row19_traceSegment_037_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 792 36 36, g32p_row19_traceSegment_037_0792_0036, g32p_row19_traceSegment_037_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 720 72 72, g32p_row19_traceSegment_037_0720_0072, g32p_row19_traceSegment_037_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_037 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 576 144 144, g32p_row19_traceSegment_037_0576_0144, g32p_row19_traceSegment_037_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 864 9 9, g32p_row19_traceSegment_037_0864_0009, g32p_row19_traceSegment_037_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 882 9 9, g32p_row19_traceSegment_037_0882_0009, g32p_row19_traceSegment_037_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 864 18 18, g32p_row19_traceSegment_037_0864_0018, g32p_row19_traceSegment_037_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 900 9 9, g32p_row19_traceSegment_037_0900_0009, g32p_row19_traceSegment_037_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 918 9 9, g32p_row19_traceSegment_037_0918_0009, g32p_row19_traceSegment_037_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 900 18 18, g32p_row19_traceSegment_037_0900_0018, g32p_row19_traceSegment_037_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 864 36 36, g32p_row19_traceSegment_037_0864_0036, g32p_row19_traceSegment_037_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 936 9 9, g32p_row19_traceSegment_037_0936_0009, g32p_row19_traceSegment_037_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 954 9 9, g32p_row19_traceSegment_037_0954_0009, g32p_row19_traceSegment_037_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 936 18 18, g32p_row19_traceSegment_037_0936_0018, g32p_row19_traceSegment_037_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 972 9 9, g32p_row19_traceSegment_037_0972_0009, g32p_row19_traceSegment_037_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 990 9 9, g32p_row19_traceSegment_037_0990_0009, g32p_row19_traceSegment_037_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 972 18 18, g32p_row19_traceSegment_037_0972_0018, g32p_row19_traceSegment_037_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 936 36 36, g32p_row19_traceSegment_037_0936_0036, g32p_row19_traceSegment_037_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 864 72 72, g32p_row19_traceSegment_037_0864_0072, g32p_row19_traceSegment_037_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1008 9 9, g32p_row19_traceSegment_037_1008_0009, g32p_row19_traceSegment_037_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1026 9 9, g32p_row19_traceSegment_037_1026_0009, g32p_row19_traceSegment_037_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1008 18 18, g32p_row19_traceSegment_037_1008_0018, g32p_row19_traceSegment_037_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1044 9 9, g32p_row19_traceSegment_037_1044_0009, g32p_row19_traceSegment_037_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1062 9 9, g32p_row19_traceSegment_037_1062_0009, g32p_row19_traceSegment_037_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1044 18 18, g32p_row19_traceSegment_037_1044_0018, g32p_row19_traceSegment_037_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1008 36 36, g32p_row19_traceSegment_037_1008_0036, g32p_row19_traceSegment_037_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1080 9 9, g32p_row19_traceSegment_037_1080_0009, g32p_row19_traceSegment_037_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1098 9 9, g32p_row19_traceSegment_037_1098_0009, g32p_row19_traceSegment_037_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1080 18 18, g32p_row19_traceSegment_037_1080_0018, g32p_row19_traceSegment_037_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1116 9 9, g32p_row19_traceSegment_037_1116_0009, g32p_row19_traceSegment_037_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_037 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_037_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_037 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1134 9 9, g32p_row19_traceSegment_037_1134_0009, g32p_row19_traceSegment_037_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_037 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1116 18 18, g32p_row19_traceSegment_037_1116_0018, g32p_row19_traceSegment_037_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_037 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1080 36 36, g32p_row19_traceSegment_037_1080_0036, g32p_row19_traceSegment_037_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_037_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_037 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 1008 72 72, g32p_row19_traceSegment_037_1008_0072, g32p_row19_traceSegment_037_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_037 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 864 144 144, g32p_row19_traceSegment_037_0864_0144, g32p_row19_traceSegment_037_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_037 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 576 288 288, g32p_row19_traceSegment_037_0576_0288, g32p_row19_traceSegment_037_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_037_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_037 0 1152 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_037 0 576 576, g32p_row19_traceSegment_037_0000_0576, g32p_row19_traceSegment_037_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_037_0000_1152

end HodgeLean.Foundations.Program

end
end
