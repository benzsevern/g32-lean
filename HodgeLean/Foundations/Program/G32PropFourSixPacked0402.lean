import HodgeLean.Foundations.Program.G32PropFourSixPacked0401
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_028 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 28 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_028_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 0 9 9, g32p_row26_traceSegment_028_0000_0009, g32p_row26_traceSegment_028_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 18 9 9, g32p_row26_traceSegment_028_0018_0009, g32p_row26_traceSegment_028_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 0 18 18, g32p_row26_traceSegment_028_0000_0018, g32p_row26_traceSegment_028_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 36 9 9, g32p_row26_traceSegment_028_0036_0009, g32p_row26_traceSegment_028_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 54 9 9, g32p_row26_traceSegment_028_0054_0009, g32p_row26_traceSegment_028_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 36 18 18, g32p_row26_traceSegment_028_0036_0018, g32p_row26_traceSegment_028_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 0 36 36, g32p_row26_traceSegment_028_0000_0036, g32p_row26_traceSegment_028_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 72 9 9, g32p_row26_traceSegment_028_0072_0009, g32p_row26_traceSegment_028_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 90 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 90 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 90 9 9, g32p_row26_traceSegment_028_0090_0009, g32p_row26_traceSegment_028_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 72 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 72 18 18, g32p_row26_traceSegment_028_0072_0018, g32p_row26_traceSegment_028_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 117 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 108 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 108 9 9, g32p_row26_traceSegment_028_0108_0009, g32p_row26_traceSegment_028_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 126 9 9, g32p_row26_traceSegment_028_0126_0009, g32p_row26_traceSegment_028_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 108 18 18, g32p_row26_traceSegment_028_0108_0018, g32p_row26_traceSegment_028_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 72 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 72 36 36, g32p_row26_traceSegment_028_0072_0036, g32p_row26_traceSegment_028_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_028 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 0 72 72, g32p_row26_traceSegment_028_0000_0072, g32p_row26_traceSegment_028_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 144 9 9, g32p_row26_traceSegment_028_0144_0009, g32p_row26_traceSegment_028_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 162 9 9, g32p_row26_traceSegment_028_0162_0009, g32p_row26_traceSegment_028_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 144 18 18, g32p_row26_traceSegment_028_0144_0018, g32p_row26_traceSegment_028_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 180 9 9, g32p_row26_traceSegment_028_0180_0009, g32p_row26_traceSegment_028_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 198 9 9, g32p_row26_traceSegment_028_0198_0009, g32p_row26_traceSegment_028_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 180 18 18, g32p_row26_traceSegment_028_0180_0018, g32p_row26_traceSegment_028_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 144 36 36, g32p_row26_traceSegment_028_0144_0036, g32p_row26_traceSegment_028_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 216 9 9, g32p_row26_traceSegment_028_0216_0009, g32p_row26_traceSegment_028_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 234 9 9, g32p_row26_traceSegment_028_0234_0009, g32p_row26_traceSegment_028_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 216 18 18, g32p_row26_traceSegment_028_0216_0018, g32p_row26_traceSegment_028_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 261 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 252 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 252 9 9, g32p_row26_traceSegment_028_0252_0009, g32p_row26_traceSegment_028_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 279 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 270 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 270 9 9, g32p_row26_traceSegment_028_0270_0009, g32p_row26_traceSegment_028_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 252 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 252 18 18, g32p_row26_traceSegment_028_0252_0018, g32p_row26_traceSegment_028_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 216 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 216 36 36, g32p_row26_traceSegment_028_0216_0036, g32p_row26_traceSegment_028_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_028 144 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 144 72 72, g32p_row26_traceSegment_028_0144_0072, g32p_row26_traceSegment_028_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_028 0 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 0 144 144, g32p_row26_traceSegment_028_0000_0144, g32p_row26_traceSegment_028_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 288 9 9, g32p_row26_traceSegment_028_0288_0009, g32p_row26_traceSegment_028_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 306 9 9, g32p_row26_traceSegment_028_0306_0009, g32p_row26_traceSegment_028_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 288 18 18, g32p_row26_traceSegment_028_0288_0018, g32p_row26_traceSegment_028_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 324 9 9, g32p_row26_traceSegment_028_0324_0009, g32p_row26_traceSegment_028_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 342 9 9, g32p_row26_traceSegment_028_0342_0009, g32p_row26_traceSegment_028_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 324 18 18, g32p_row26_traceSegment_028_0324_0018, g32p_row26_traceSegment_028_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 288 36 36, g32p_row26_traceSegment_028_0288_0036, g32p_row26_traceSegment_028_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 360 9 9, g32p_row26_traceSegment_028_0360_0009, g32p_row26_traceSegment_028_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 378 9 9, g32p_row26_traceSegment_028_0378_0009, g32p_row26_traceSegment_028_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 360 18 18, g32p_row26_traceSegment_028_0360_0018, g32p_row26_traceSegment_028_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 396 9 9, g32p_row26_traceSegment_028_0396_0009, g32p_row26_traceSegment_028_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 414 9 9, g32p_row26_traceSegment_028_0414_0009, g32p_row26_traceSegment_028_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 396 18 18, g32p_row26_traceSegment_028_0396_0018, g32p_row26_traceSegment_028_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 360 36 36, g32p_row26_traceSegment_028_0360_0036, g32p_row26_traceSegment_028_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_028 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 288 72 72, g32p_row26_traceSegment_028_0288_0072, g32p_row26_traceSegment_028_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 432 9 9, g32p_row26_traceSegment_028_0432_0009, g32p_row26_traceSegment_028_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 450 9 9, g32p_row26_traceSegment_028_0450_0009, g32p_row26_traceSegment_028_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 432 18 18, g32p_row26_traceSegment_028_0432_0018, g32p_row26_traceSegment_028_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 468 9 9, g32p_row26_traceSegment_028_0468_0009, g32p_row26_traceSegment_028_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 486 9 9, g32p_row26_traceSegment_028_0486_0009, g32p_row26_traceSegment_028_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 468 18 18, g32p_row26_traceSegment_028_0468_0018, g32p_row26_traceSegment_028_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 432 36 36, g32p_row26_traceSegment_028_0432_0036, g32p_row26_traceSegment_028_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 504 9 9, g32p_row26_traceSegment_028_0504_0009, g32p_row26_traceSegment_028_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 522 9 9, g32p_row26_traceSegment_028_0522_0009, g32p_row26_traceSegment_028_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 504 18 18, g32p_row26_traceSegment_028_0504_0018, g32p_row26_traceSegment_028_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 540 9 9, g32p_row26_traceSegment_028_0540_0009, g32p_row26_traceSegment_028_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_028 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_028_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_028 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 558 9 9, g32p_row26_traceSegment_028_0558_0009, g32p_row26_traceSegment_028_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_028 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 540 18 18, g32p_row26_traceSegment_028_0540_0018, g32p_row26_traceSegment_028_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_028 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 504 36 36, g32p_row26_traceSegment_028_0504_0036, g32p_row26_traceSegment_028_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_028 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 432 72 72, g32p_row26_traceSegment_028_0432_0072, g32p_row26_traceSegment_028_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_028 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 288 144 144, g32p_row26_traceSegment_028_0288_0144, g32p_row26_traceSegment_028_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_028_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_028 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_028 0 288 288, g32p_row26_traceSegment_028_0000_0288, g32p_row26_traceSegment_028_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 28 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_028_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_031 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 31 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_031_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 9 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 0 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 0 9 9, g32p_row26_traceSegment_031_0000_0009, g32p_row26_traceSegment_031_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 27 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 18 9 9, g32p_row26_traceSegment_031_0018_0009, g32p_row26_traceSegment_031_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 0 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 0 18 18, g32p_row26_traceSegment_031_0000_0018, g32p_row26_traceSegment_031_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 36 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 36 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 36 9 9, g32p_row26_traceSegment_031_0036_0009, g32p_row26_traceSegment_031_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 63 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 54 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 54 9 9, g32p_row26_traceSegment_031_0054_0009, g32p_row26_traceSegment_031_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 36 36 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 36 18 18, g32p_row26_traceSegment_031_0036_0018, g32p_row26_traceSegment_031_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 0 72 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 0 36 36, g32p_row26_traceSegment_031_0000_0036, g32p_row26_traceSegment_031_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 72 9 9, g32p_row26_traceSegment_031_0072_0009, g32p_row26_traceSegment_031_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 90 9 9, g32p_row26_traceSegment_031_0090_0009, g32p_row26_traceSegment_031_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 72 18 18, g32p_row26_traceSegment_031_0072_0018, g32p_row26_traceSegment_031_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 108 9 9, g32p_row26_traceSegment_031_0108_0009, g32p_row26_traceSegment_031_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 126 9 9, g32p_row26_traceSegment_031_0126_0009, g32p_row26_traceSegment_031_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 108 18 18, g32p_row26_traceSegment_031_0108_0018, g32p_row26_traceSegment_031_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 72 36 36, g32p_row26_traceSegment_031_0072_0036, g32p_row26_traceSegment_031_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_031 0 144 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 0 72 72, g32p_row26_traceSegment_031_0000_0072, g32p_row26_traceSegment_031_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 144 9 9, g32p_row26_traceSegment_031_0144_0009, g32p_row26_traceSegment_031_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 162 9 9, g32p_row26_traceSegment_031_0162_0009, g32p_row26_traceSegment_031_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 144 18 18, g32p_row26_traceSegment_031_0144_0018, g32p_row26_traceSegment_031_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 180 9 9, g32p_row26_traceSegment_031_0180_0009, g32p_row26_traceSegment_031_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 198 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 198 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 198 9 9, g32p_row26_traceSegment_031_0198_0009, g32p_row26_traceSegment_031_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 180 18 18, g32p_row26_traceSegment_031_0180_0018, g32p_row26_traceSegment_031_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 144 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 144 36 36, g32p_row26_traceSegment_031_0144_0036, g32p_row26_traceSegment_031_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 216 9 9, g32p_row26_traceSegment_031_0216_0009, g32p_row26_traceSegment_031_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 234 9 9, g32p_row26_traceSegment_031_0234_0009, g32p_row26_traceSegment_031_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 216 18 18, g32p_row26_traceSegment_031_0216_0018, g32p_row26_traceSegment_031_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 252 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 252 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 252 9 9, g32p_row26_traceSegment_031_0252_0009, g32p_row26_traceSegment_031_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 270 9 9, g32p_row26_traceSegment_031_0270_0009, g32p_row26_traceSegment_031_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 252 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 252 18 18, g32p_row26_traceSegment_031_0252_0018, g32p_row26_traceSegment_031_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 216 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 216 36 36, g32p_row26_traceSegment_031_0216_0036, g32p_row26_traceSegment_031_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_031 144 144 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 144 72 72, g32p_row26_traceSegment_031_0144_0072, g32p_row26_traceSegment_031_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_031 0 288 = [0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 0 144 144, g32p_row26_traceSegment_031_0000_0144, g32p_row26_traceSegment_031_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 288 9 9, g32p_row26_traceSegment_031_0288_0009, g32p_row26_traceSegment_031_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 306 9 9, g32p_row26_traceSegment_031_0306_0009, g32p_row26_traceSegment_031_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 288 18 18, g32p_row26_traceSegment_031_0288_0018, g32p_row26_traceSegment_031_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 324 9 9, g32p_row26_traceSegment_031_0324_0009, g32p_row26_traceSegment_031_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 342 9 9, g32p_row26_traceSegment_031_0342_0009, g32p_row26_traceSegment_031_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 324 18 18, g32p_row26_traceSegment_031_0324_0018, g32p_row26_traceSegment_031_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 288 36 36, g32p_row26_traceSegment_031_0288_0036, g32p_row26_traceSegment_031_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 360 9 9, g32p_row26_traceSegment_031_0360_0009, g32p_row26_traceSegment_031_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 378 9 9, g32p_row26_traceSegment_031_0378_0009, g32p_row26_traceSegment_031_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 360 18 18, g32p_row26_traceSegment_031_0360_0018, g32p_row26_traceSegment_031_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 396 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 396 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 396 9 9, g32p_row26_traceSegment_031_0396_0009, g32p_row26_traceSegment_031_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 414 9 9, g32p_row26_traceSegment_031_0414_0009, g32p_row26_traceSegment_031_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 396 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 396 18 18, g32p_row26_traceSegment_031_0396_0018, g32p_row26_traceSegment_031_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 360 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 360 36 36, g32p_row26_traceSegment_031_0360_0036, g32p_row26_traceSegment_031_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_031 288 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 288 72 72, g32p_row26_traceSegment_031_0288_0072, g32p_row26_traceSegment_031_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 432 9 9, g32p_row26_traceSegment_031_0432_0009, g32p_row26_traceSegment_031_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 450 9 9, g32p_row26_traceSegment_031_0450_0009, g32p_row26_traceSegment_031_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 432 18 18, g32p_row26_traceSegment_031_0432_0018, g32p_row26_traceSegment_031_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 468 9 9, g32p_row26_traceSegment_031_0468_0009, g32p_row26_traceSegment_031_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 486 9 9, g32p_row26_traceSegment_031_0486_0009, g32p_row26_traceSegment_031_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 468 18 18, g32p_row26_traceSegment_031_0468_0018, g32p_row26_traceSegment_031_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 432 36 36, g32p_row26_traceSegment_031_0432_0036, g32p_row26_traceSegment_031_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 504 9 9, g32p_row26_traceSegment_031_0504_0009, g32p_row26_traceSegment_031_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 522 9 9, g32p_row26_traceSegment_031_0522_0009, g32p_row26_traceSegment_031_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 504 18 18, g32p_row26_traceSegment_031_0504_0018, g32p_row26_traceSegment_031_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 540 9 9, g32p_row26_traceSegment_031_0540_0009, g32p_row26_traceSegment_031_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_031 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_031_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_031 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 558 9 9, g32p_row26_traceSegment_031_0558_0009, g32p_row26_traceSegment_031_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_031 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 540 18 18, g32p_row26_traceSegment_031_0540_0018, g32p_row26_traceSegment_031_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_031 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 504 36 36, g32p_row26_traceSegment_031_0504_0036, g32p_row26_traceSegment_031_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_031 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 432 72 72, g32p_row26_traceSegment_031_0432_0072, g32p_row26_traceSegment_031_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_031 288 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 288 144 144, g32p_row26_traceSegment_031_0288_0144, g32p_row26_traceSegment_031_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_031_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_031 0 576 = [0, 4, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_031 0 288 288, g32p_row26_traceSegment_031_0000_0288, g32p_row26_traceSegment_031_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 31 = [0, 4, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_031_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 17) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 17) (g32p_literalTraceValue 25 17)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_017]
  decide +kernel

theorem g32p_row26_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 18) (g32p_literalTraceValue 25 18)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_018]
  decide +kernel

theorem g32p_row26_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 19) (g32p_literalTraceValue 25 19)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_019]
  decide +kernel

theorem g32p_row26_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 20) (g32p_literalTraceValue 25 20)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_020]
  decide +kernel

theorem g32p_row26_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 23) (g32p_literalTraceValue 25 23)
      [1, -1, 1] [1728, 1728, 1728] = true := by
  rw [g32p_row26_traceCoefficients_023]
  decide +kernel

theorem g32p_row26_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 27) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 27) (g32p_literalTraceValue 25 27)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_027]
  decide +kernel

theorem g32p_row26_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 28) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 28) (g32p_literalTraceValue 25 28)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_028]
  decide +kernel

theorem g32p_row26_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 31) (g32p_literalTraceValue 25 31)
      [1, -1, 1] [1152, 2304, 2304] = true := by
  rw [g32p_row26_traceCoefficients_031]
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

private def g32p_row26_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_034_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 0 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 0 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 0 9 9, g32p_row26_traceSegment_034_0000_0009, g32p_row26_traceSegment_034_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 27 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 18 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 18 9 9, g32p_row26_traceSegment_034_0018_0009, g32p_row26_traceSegment_034_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 0 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 0 18 18, g32p_row26_traceSegment_034_0000_0018, g32p_row26_traceSegment_034_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 36 9 9, g32p_row26_traceSegment_034_0036_0009, g32p_row26_traceSegment_034_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 54 9 9, g32p_row26_traceSegment_034_0054_0009, g32p_row26_traceSegment_034_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 36 18 18, g32p_row26_traceSegment_034_0036_0018, g32p_row26_traceSegment_034_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 0 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 0 36 36, g32p_row26_traceSegment_034_0000_0036, g32p_row26_traceSegment_034_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 72 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 81 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 72 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 72 9 9, g32p_row26_traceSegment_034_0072_0009, g32p_row26_traceSegment_034_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 90 9 9, g32p_row26_traceSegment_034_0090_0009, g32p_row26_traceSegment_034_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 72 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 72 18 18, g32p_row26_traceSegment_034_0072_0018, g32p_row26_traceSegment_034_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 108 9 9, g32p_row26_traceSegment_034_0108_0009, g32p_row26_traceSegment_034_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 126 9 9, g32p_row26_traceSegment_034_0126_0009, g32p_row26_traceSegment_034_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 108 18 18, g32p_row26_traceSegment_034_0108_0018, g32p_row26_traceSegment_034_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 72 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 72 36 36, g32p_row26_traceSegment_034_0072_0036, g32p_row26_traceSegment_034_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_034 0 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 0 72 72, g32p_row26_traceSegment_034_0000_0072, g32p_row26_traceSegment_034_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 144 9 9, g32p_row26_traceSegment_034_0144_0009, g32p_row26_traceSegment_034_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 162 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 171 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 162 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 162 9 9, g32p_row26_traceSegment_034_0162_0009, g32p_row26_traceSegment_034_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 144 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 144 18 18, g32p_row26_traceSegment_034_0144_0018, g32p_row26_traceSegment_034_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 189 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 180 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 180 9 9, g32p_row26_traceSegment_034_0180_0009, g32p_row26_traceSegment_034_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 198 9 9, g32p_row26_traceSegment_034_0198_0009, g32p_row26_traceSegment_034_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 180 18 18, g32p_row26_traceSegment_034_0180_0018, g32p_row26_traceSegment_034_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 144 72 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 144 36 36, g32p_row26_traceSegment_034_0144_0036, g32p_row26_traceSegment_034_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 216 9 9, g32p_row26_traceSegment_034_0216_0009, g32p_row26_traceSegment_034_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 243 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 234 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 234 9 9, g32p_row26_traceSegment_034_0234_0009, g32p_row26_traceSegment_034_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 216 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 216 18 18, g32p_row26_traceSegment_034_0216_0018, g32p_row26_traceSegment_034_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 252 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 252 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 252 9 9, g32p_row26_traceSegment_034_0252_0009, g32p_row26_traceSegment_034_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 270 9 9, g32p_row26_traceSegment_034_0270_0009, g32p_row26_traceSegment_034_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 252 18 18, g32p_row26_traceSegment_034_0252_0018, g32p_row26_traceSegment_034_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 216 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 216 36 36, g32p_row26_traceSegment_034_0216_0036, g32p_row26_traceSegment_034_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_034 144 144 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 144 72 72, g32p_row26_traceSegment_034_0144_0072, g32p_row26_traceSegment_034_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_034 0 288 = [0, 9, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 0 144 144, g32p_row26_traceSegment_034_0000_0144, g32p_row26_traceSegment_034_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 288 9 9, g32p_row26_traceSegment_034_0288_0009, g32p_row26_traceSegment_034_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 306 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 306 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 306 9 9, g32p_row26_traceSegment_034_0306_0009, g32p_row26_traceSegment_034_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 288 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 288 18 18, g32p_row26_traceSegment_034_0288_0018, g32p_row26_traceSegment_034_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 324 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 333 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 324 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 324 9 9, g32p_row26_traceSegment_034_0324_0009, g32p_row26_traceSegment_034_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 342 9 9, g32p_row26_traceSegment_034_0342_0009, g32p_row26_traceSegment_034_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 324 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 324 18 18, g32p_row26_traceSegment_034_0324_0018, g32p_row26_traceSegment_034_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 288 72 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 288 36 36, g32p_row26_traceSegment_034_0288_0036, g32p_row26_traceSegment_034_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 360 9 9, g32p_row26_traceSegment_034_0360_0009, g32p_row26_traceSegment_034_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 378 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 378 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 378 9 9, g32p_row26_traceSegment_034_0378_0009, g32p_row26_traceSegment_034_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 360 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 360 18 18, g32p_row26_traceSegment_034_0360_0018, g32p_row26_traceSegment_034_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 396 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 405 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 396 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 396 9 9, g32p_row26_traceSegment_034_0396_0009, g32p_row26_traceSegment_034_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 414 9 9, g32p_row26_traceSegment_034_0414_0009, g32p_row26_traceSegment_034_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 396 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 396 18 18, g32p_row26_traceSegment_034_0396_0018, g32p_row26_traceSegment_034_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 360 72 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 360 36 36, g32p_row26_traceSegment_034_0360_0036, g32p_row26_traceSegment_034_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_034 288 144 = [0, 7, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 288 72 72, g32p_row26_traceSegment_034_0288_0072, g32p_row26_traceSegment_034_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 432 9 9, g32p_row26_traceSegment_034_0432_0009, g32p_row26_traceSegment_034_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 450 9 9, g32p_row26_traceSegment_034_0450_0009, g32p_row26_traceSegment_034_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 432 18 18, g32p_row26_traceSegment_034_0432_0018, g32p_row26_traceSegment_034_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 477 9 = [0, 2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 468 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 468 9 9, g32p_row26_traceSegment_034_0468_0009, g32p_row26_traceSegment_034_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 486 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 486 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 486 9 9, g32p_row26_traceSegment_034_0486_0009, g32p_row26_traceSegment_034_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 468 36 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 468 18 18, g32p_row26_traceSegment_034_0468_0018, g32p_row26_traceSegment_034_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 432 72 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 432 36 36, g32p_row26_traceSegment_034_0432_0036, g32p_row26_traceSegment_034_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 504 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 513 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 504 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 504 9 9, g32p_row26_traceSegment_034_0504_0009, g32p_row26_traceSegment_034_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 522 9 = [0, 2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 522 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 522 9 9, g32p_row26_traceSegment_034_0522_0009, g32p_row26_traceSegment_034_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 504 36 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 504 18 18, g32p_row26_traceSegment_034_0504_0018, g32p_row26_traceSegment_034_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 540 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 540 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 540 9 9, g32p_row26_traceSegment_034_0540_0009, g32p_row26_traceSegment_034_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 558 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_034 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_034_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_034 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 558 9 9, g32p_row26_traceSegment_034_0558_0009, g32p_row26_traceSegment_034_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_034 540 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 540 18 18, g32p_row26_traceSegment_034_0540_0018, g32p_row26_traceSegment_034_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_034 504 72 = [0, 6, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 504 36 36, g32p_row26_traceSegment_034_0504_0036, g32p_row26_traceSegment_034_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_034 432 144 = [0, 8, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 432 72 72, g32p_row26_traceSegment_034_0432_0072, g32p_row26_traceSegment_034_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_034 288 288 = [0, 15, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 288 144 144, g32p_row26_traceSegment_034_0288_0144, g32p_row26_traceSegment_034_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_034_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_034 0 576 = [0, 24, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_034 0 288 288, g32p_row26_traceSegment_034_0000_0288, g32p_row26_traceSegment_034_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 34 = [0, 24, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_034_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_037_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 0 9 9, g32p_row26_traceSegment_037_0000_0009, g32p_row26_traceSegment_037_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 18 9 9, g32p_row26_traceSegment_037_0018_0009, g32p_row26_traceSegment_037_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 0 18 18, g32p_row26_traceSegment_037_0000_0018, g32p_row26_traceSegment_037_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 36 9 9, g32p_row26_traceSegment_037_0036_0009, g32p_row26_traceSegment_037_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 54 9 9, g32p_row26_traceSegment_037_0054_0009, g32p_row26_traceSegment_037_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 36 18 18, g32p_row26_traceSegment_037_0036_0018, g32p_row26_traceSegment_037_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 0 36 36, g32p_row26_traceSegment_037_0000_0036, g32p_row26_traceSegment_037_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 72 9 9, g32p_row26_traceSegment_037_0072_0009, g32p_row26_traceSegment_037_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 90 9 9, g32p_row26_traceSegment_037_0090_0009, g32p_row26_traceSegment_037_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 72 18 18, g32p_row26_traceSegment_037_0072_0018, g32p_row26_traceSegment_037_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 108 9 9, g32p_row26_traceSegment_037_0108_0009, g32p_row26_traceSegment_037_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 135 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 126 9 9, g32p_row26_traceSegment_037_0126_0009, g32p_row26_traceSegment_037_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 108 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 108 18 18, g32p_row26_traceSegment_037_0108_0018, g32p_row26_traceSegment_037_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 72 36 36, g32p_row26_traceSegment_037_0072_0036, g32p_row26_traceSegment_037_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_037 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 0 72 72, g32p_row26_traceSegment_037_0000_0072, g32p_row26_traceSegment_037_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 144 9 9, g32p_row26_traceSegment_037_0144_0009, g32p_row26_traceSegment_037_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 162 9 9, g32p_row26_traceSegment_037_0162_0009, g32p_row26_traceSegment_037_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 144 18 18, g32p_row26_traceSegment_037_0144_0018, g32p_row26_traceSegment_037_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 180 9 9, g32p_row26_traceSegment_037_0180_0009, g32p_row26_traceSegment_037_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 198 9 9, g32p_row26_traceSegment_037_0198_0009, g32p_row26_traceSegment_037_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 180 18 18, g32p_row26_traceSegment_037_0180_0018, g32p_row26_traceSegment_037_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 144 36 36, g32p_row26_traceSegment_037_0144_0036, g32p_row26_traceSegment_037_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 216 9 9, g32p_row26_traceSegment_037_0216_0009, g32p_row26_traceSegment_037_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 234 9 9, g32p_row26_traceSegment_037_0234_0009, g32p_row26_traceSegment_037_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 216 18 18, g32p_row26_traceSegment_037_0216_0018, g32p_row26_traceSegment_037_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 252 9 9, g32p_row26_traceSegment_037_0252_0009, g32p_row26_traceSegment_037_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 270 9 9, g32p_row26_traceSegment_037_0270_0009, g32p_row26_traceSegment_037_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 252 18 18, g32p_row26_traceSegment_037_0252_0018, g32p_row26_traceSegment_037_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 216 36 36, g32p_row26_traceSegment_037_0216_0036, g32p_row26_traceSegment_037_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_037 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 144 72 72, g32p_row26_traceSegment_037_0144_0072, g32p_row26_traceSegment_037_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_037 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 0 144 144, g32p_row26_traceSegment_037_0000_0144, g32p_row26_traceSegment_037_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 288 9 9, g32p_row26_traceSegment_037_0288_0009, g32p_row26_traceSegment_037_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 306 9 9, g32p_row26_traceSegment_037_0306_0009, g32p_row26_traceSegment_037_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 288 18 18, g32p_row26_traceSegment_037_0288_0018, g32p_row26_traceSegment_037_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 324 9 9, g32p_row26_traceSegment_037_0324_0009, g32p_row26_traceSegment_037_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 342 9 9, g32p_row26_traceSegment_037_0342_0009, g32p_row26_traceSegment_037_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 324 18 18, g32p_row26_traceSegment_037_0324_0018, g32p_row26_traceSegment_037_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 288 36 36, g32p_row26_traceSegment_037_0288_0036, g32p_row26_traceSegment_037_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 360 9 9, g32p_row26_traceSegment_037_0360_0009, g32p_row26_traceSegment_037_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 378 9 9, g32p_row26_traceSegment_037_0378_0009, g32p_row26_traceSegment_037_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 360 18 18, g32p_row26_traceSegment_037_0360_0018, g32p_row26_traceSegment_037_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 396 9 9, g32p_row26_traceSegment_037_0396_0009, g32p_row26_traceSegment_037_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 414 9 9, g32p_row26_traceSegment_037_0414_0009, g32p_row26_traceSegment_037_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 396 18 18, g32p_row26_traceSegment_037_0396_0018, g32p_row26_traceSegment_037_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 360 36 36, g32p_row26_traceSegment_037_0360_0036, g32p_row26_traceSegment_037_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_037 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 288 72 72, g32p_row26_traceSegment_037_0288_0072, g32p_row26_traceSegment_037_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 432 9 9, g32p_row26_traceSegment_037_0432_0009, g32p_row26_traceSegment_037_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 450 9 9, g32p_row26_traceSegment_037_0450_0009, g32p_row26_traceSegment_037_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 432 18 18, g32p_row26_traceSegment_037_0432_0018, g32p_row26_traceSegment_037_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 468 9 9, g32p_row26_traceSegment_037_0468_0009, g32p_row26_traceSegment_037_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 486 9 9, g32p_row26_traceSegment_037_0486_0009, g32p_row26_traceSegment_037_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 468 18 18, g32p_row26_traceSegment_037_0468_0018, g32p_row26_traceSegment_037_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 432 36 36, g32p_row26_traceSegment_037_0432_0036, g32p_row26_traceSegment_037_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 504 9 9, g32p_row26_traceSegment_037_0504_0009, g32p_row26_traceSegment_037_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 522 9 9, g32p_row26_traceSegment_037_0522_0009, g32p_row26_traceSegment_037_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 504 18 18, g32p_row26_traceSegment_037_0504_0018, g32p_row26_traceSegment_037_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 540 9 9, g32p_row26_traceSegment_037_0540_0009, g32p_row26_traceSegment_037_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_037 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_037_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_037 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 558 9 9, g32p_row26_traceSegment_037_0558_0009, g32p_row26_traceSegment_037_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_037 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 540 18 18, g32p_row26_traceSegment_037_0540_0018, g32p_row26_traceSegment_037_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_037 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 504 36 36, g32p_row26_traceSegment_037_0504_0036, g32p_row26_traceSegment_037_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_037 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 432 72 72, g32p_row26_traceSegment_037_0432_0072, g32p_row26_traceSegment_037_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_037 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 288 144 144, g32p_row26_traceSegment_037_0288_0144, g32p_row26_traceSegment_037_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_037_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_037 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_037 0 288 288, g32p_row26_traceSegment_037_0000_0288, g32p_row26_traceSegment_037_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_037_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_041 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 41 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_041_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 0 9 9, g32p_row26_traceSegment_041_0000_0009, g32p_row26_traceSegment_041_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 18 9 9, g32p_row26_traceSegment_041_0018_0009, g32p_row26_traceSegment_041_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 0 18 18, g32p_row26_traceSegment_041_0000_0018, g32p_row26_traceSegment_041_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 36 9 9, g32p_row26_traceSegment_041_0036_0009, g32p_row26_traceSegment_041_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 54 9 9, g32p_row26_traceSegment_041_0054_0009, g32p_row26_traceSegment_041_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 36 18 18, g32p_row26_traceSegment_041_0036_0018, g32p_row26_traceSegment_041_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 0 36 36, g32p_row26_traceSegment_041_0000_0036, g32p_row26_traceSegment_041_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 72 9 9, g32p_row26_traceSegment_041_0072_0009, g32p_row26_traceSegment_041_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 90 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 90 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 90 9 9, g32p_row26_traceSegment_041_0090_0009, g32p_row26_traceSegment_041_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 72 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 72 18 18, g32p_row26_traceSegment_041_0072_0018, g32p_row26_traceSegment_041_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 108 9 9, g32p_row26_traceSegment_041_0108_0009, g32p_row26_traceSegment_041_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 126 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 126 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 126 9 9, g32p_row26_traceSegment_041_0126_0009, g32p_row26_traceSegment_041_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 108 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 108 18 18, g32p_row26_traceSegment_041_0108_0018, g32p_row26_traceSegment_041_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 72 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 72 36 36, g32p_row26_traceSegment_041_0072_0036, g32p_row26_traceSegment_041_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_041 0 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 0 72 72, g32p_row26_traceSegment_041_0000_0072, g32p_row26_traceSegment_041_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 144 9 9, g32p_row26_traceSegment_041_0144_0009, g32p_row26_traceSegment_041_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 162 9 9, g32p_row26_traceSegment_041_0162_0009, g32p_row26_traceSegment_041_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 144 18 18, g32p_row26_traceSegment_041_0144_0018, g32p_row26_traceSegment_041_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 180 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 180 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 180 9 9, g32p_row26_traceSegment_041_0180_0009, g32p_row26_traceSegment_041_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 198 9 9, g32p_row26_traceSegment_041_0198_0009, g32p_row26_traceSegment_041_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 180 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 180 18 18, g32p_row26_traceSegment_041_0180_0018, g32p_row26_traceSegment_041_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 144 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 144 36 36, g32p_row26_traceSegment_041_0144_0036, g32p_row26_traceSegment_041_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 216 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 225 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 216 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 216 9 9, g32p_row26_traceSegment_041_0216_0009, g32p_row26_traceSegment_041_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 234 9 9, g32p_row26_traceSegment_041_0234_0009, g32p_row26_traceSegment_041_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 216 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 216 18 18, g32p_row26_traceSegment_041_0216_0018, g32p_row26_traceSegment_041_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 252 9 9, g32p_row26_traceSegment_041_0252_0009, g32p_row26_traceSegment_041_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 279 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 270 9 9, g32p_row26_traceSegment_041_0270_0009, g32p_row26_traceSegment_041_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 252 18 18, g32p_row26_traceSegment_041_0252_0018, g32p_row26_traceSegment_041_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 216 72 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 216 36 36, g32p_row26_traceSegment_041_0216_0036, g32p_row26_traceSegment_041_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_041 144 144 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 144 72 72, g32p_row26_traceSegment_041_0144_0072, g32p_row26_traceSegment_041_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_041 0 288 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 0 144 144, g32p_row26_traceSegment_041_0000_0144, g32p_row26_traceSegment_041_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 288 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 288 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 288 9 9, g32p_row26_traceSegment_041_0288_0009, g32p_row26_traceSegment_041_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 306 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 306 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 306 9 9, g32p_row26_traceSegment_041_0306_0009, g32p_row26_traceSegment_041_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 288 36 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 288 18 18, g32p_row26_traceSegment_041_0288_0018, g32p_row26_traceSegment_041_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 324 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 333 9 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 324 18 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 324 9 9, g32p_row26_traceSegment_041_0324_0009, g32p_row26_traceSegment_041_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 342 9 9, g32p_row26_traceSegment_041_0342_0009, g32p_row26_traceSegment_041_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 324 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 324 18 18, g32p_row26_traceSegment_041_0324_0018, g32p_row26_traceSegment_041_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 288 72 = [0, 0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 288 36 36, g32p_row26_traceSegment_041_0288_0036, g32p_row26_traceSegment_041_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 360 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 360 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 360 9 9, g32p_row26_traceSegment_041_0360_0009, g32p_row26_traceSegment_041_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 387 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 378 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 378 9 9, g32p_row26_traceSegment_041_0378_0009, g32p_row26_traceSegment_041_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 360 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 360 18 18, g32p_row26_traceSegment_041_0360_0018, g32p_row26_traceSegment_041_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 396 9 9, g32p_row26_traceSegment_041_0396_0009, g32p_row26_traceSegment_041_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 414 9 9, g32p_row26_traceSegment_041_0414_0009, g32p_row26_traceSegment_041_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 396 18 18, g32p_row26_traceSegment_041_0396_0018, g32p_row26_traceSegment_041_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 360 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 360 36 36, g32p_row26_traceSegment_041_0360_0036, g32p_row26_traceSegment_041_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_041 288 144 = [0, 0, 3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 288 72 72, g32p_row26_traceSegment_041_0288_0072, g32p_row26_traceSegment_041_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 432 9 9, g32p_row26_traceSegment_041_0432_0009, g32p_row26_traceSegment_041_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 450 9 9, g32p_row26_traceSegment_041_0450_0009, g32p_row26_traceSegment_041_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 432 18 18, g32p_row26_traceSegment_041_0432_0018, g32p_row26_traceSegment_041_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 477 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 468 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 468 9 9, g32p_row26_traceSegment_041_0468_0009, g32p_row26_traceSegment_041_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 486 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 495 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 486 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 486 9 9, g32p_row26_traceSegment_041_0486_0009, g32p_row26_traceSegment_041_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 468 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 468 18 18, g32p_row26_traceSegment_041_0468_0018, g32p_row26_traceSegment_041_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 432 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 432 36 36, g32p_row26_traceSegment_041_0432_0036, g32p_row26_traceSegment_041_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 513 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 504 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 504 9 9, g32p_row26_traceSegment_041_0504_0009, g32p_row26_traceSegment_041_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 522 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 531 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 522 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 522 9 9, g32p_row26_traceSegment_041_0522_0009, g32p_row26_traceSegment_041_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 504 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 504 18 18, g32p_row26_traceSegment_041_0504_0018, g32p_row26_traceSegment_041_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 540 9 9, g32p_row26_traceSegment_041_0540_0009, g32p_row26_traceSegment_041_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_041 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_041_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_041 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 558 9 9, g32p_row26_traceSegment_041_0558_0009, g32p_row26_traceSegment_041_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_041 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 540 18 18, g32p_row26_traceSegment_041_0540_0018, g32p_row26_traceSegment_041_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_041 504 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 504 36 36, g32p_row26_traceSegment_041_0504_0036, g32p_row26_traceSegment_041_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_041 432 144 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 432 72 72, g32p_row26_traceSegment_041_0432_0072, g32p_row26_traceSegment_041_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_041 288 288 = [0, 0, 7, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 288 144 144, g32p_row26_traceSegment_041_0288_0144, g32p_row26_traceSegment_041_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_041_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_041 0 576 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_041 0 288 288, g32p_row26_traceSegment_041_0000_0288, g32p_row26_traceSegment_041_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 41 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_041_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_044_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 0 9 9, g32p_row26_traceSegment_044_0000_0009, g32p_row26_traceSegment_044_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 18 9 9, g32p_row26_traceSegment_044_0018_0009, g32p_row26_traceSegment_044_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 0 18 18, g32p_row26_traceSegment_044_0000_0018, g32p_row26_traceSegment_044_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 36 9 9, g32p_row26_traceSegment_044_0036_0009, g32p_row26_traceSegment_044_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 54 9 9, g32p_row26_traceSegment_044_0054_0009, g32p_row26_traceSegment_044_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 36 18 18, g32p_row26_traceSegment_044_0036_0018, g32p_row26_traceSegment_044_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 0 36 36, g32p_row26_traceSegment_044_0000_0036, g32p_row26_traceSegment_044_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 72 9 9, g32p_row26_traceSegment_044_0072_0009, g32p_row26_traceSegment_044_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 90 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 90 9 9, g32p_row26_traceSegment_044_0090_0009, g32p_row26_traceSegment_044_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 72 18 18, g32p_row26_traceSegment_044_0072_0018, g32p_row26_traceSegment_044_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 108 9 9, g32p_row26_traceSegment_044_0108_0009, g32p_row26_traceSegment_044_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 126 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 135 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 126 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 126 9 9, g32p_row26_traceSegment_044_0126_0009, g32p_row26_traceSegment_044_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 108 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 108 18 18, g32p_row26_traceSegment_044_0108_0018, g32p_row26_traceSegment_044_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 72 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 72 36 36, g32p_row26_traceSegment_044_0072_0036, g32p_row26_traceSegment_044_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_044 0 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 0 72 72, g32p_row26_traceSegment_044_0000_0072, g32p_row26_traceSegment_044_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 144 9 9, g32p_row26_traceSegment_044_0144_0009, g32p_row26_traceSegment_044_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 162 9 9, g32p_row26_traceSegment_044_0162_0009, g32p_row26_traceSegment_044_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 144 18 18, g32p_row26_traceSegment_044_0144_0018, g32p_row26_traceSegment_044_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 180 9 9, g32p_row26_traceSegment_044_0180_0009, g32p_row26_traceSegment_044_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 198 9 9, g32p_row26_traceSegment_044_0198_0009, g32p_row26_traceSegment_044_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 180 18 18, g32p_row26_traceSegment_044_0180_0018, g32p_row26_traceSegment_044_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 144 36 36, g32p_row26_traceSegment_044_0144_0036, g32p_row26_traceSegment_044_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 216 9 9, g32p_row26_traceSegment_044_0216_0009, g32p_row26_traceSegment_044_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 234 9 9, g32p_row26_traceSegment_044_0234_0009, g32p_row26_traceSegment_044_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 216 18 18, g32p_row26_traceSegment_044_0216_0018, g32p_row26_traceSegment_044_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 252 9 9, g32p_row26_traceSegment_044_0252_0009, g32p_row26_traceSegment_044_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 270 9 9, g32p_row26_traceSegment_044_0270_0009, g32p_row26_traceSegment_044_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 252 18 18, g32p_row26_traceSegment_044_0252_0018, g32p_row26_traceSegment_044_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 216 36 36, g32p_row26_traceSegment_044_0216_0036, g32p_row26_traceSegment_044_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_044 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 144 72 72, g32p_row26_traceSegment_044_0144_0072, g32p_row26_traceSegment_044_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_044 0 288 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 0 144 144, g32p_row26_traceSegment_044_0000_0144, g32p_row26_traceSegment_044_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 288 9 9, g32p_row26_traceSegment_044_0288_0009, g32p_row26_traceSegment_044_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 306 9 9, g32p_row26_traceSegment_044_0306_0009, g32p_row26_traceSegment_044_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 288 18 18, g32p_row26_traceSegment_044_0288_0018, g32p_row26_traceSegment_044_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 324 9 9, g32p_row26_traceSegment_044_0324_0009, g32p_row26_traceSegment_044_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 342 9 9, g32p_row26_traceSegment_044_0342_0009, g32p_row26_traceSegment_044_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 324 18 18, g32p_row26_traceSegment_044_0324_0018, g32p_row26_traceSegment_044_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 288 36 36, g32p_row26_traceSegment_044_0288_0036, g32p_row26_traceSegment_044_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 360 9 9, g32p_row26_traceSegment_044_0360_0009, g32p_row26_traceSegment_044_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 378 9 9, g32p_row26_traceSegment_044_0378_0009, g32p_row26_traceSegment_044_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 360 18 18, g32p_row26_traceSegment_044_0360_0018, g32p_row26_traceSegment_044_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 396 9 9, g32p_row26_traceSegment_044_0396_0009, g32p_row26_traceSegment_044_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 414 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 414 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 414 9 9, g32p_row26_traceSegment_044_0414_0009, g32p_row26_traceSegment_044_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 396 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 396 18 18, g32p_row26_traceSegment_044_0396_0018, g32p_row26_traceSegment_044_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 360 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 360 36 36, g32p_row26_traceSegment_044_0360_0036, g32p_row26_traceSegment_044_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_044 288 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 288 72 72, g32p_row26_traceSegment_044_0288_0072, g32p_row26_traceSegment_044_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 432 9 9, g32p_row26_traceSegment_044_0432_0009, g32p_row26_traceSegment_044_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 450 9 9, g32p_row26_traceSegment_044_0450_0009, g32p_row26_traceSegment_044_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 432 18 18, g32p_row26_traceSegment_044_0432_0018, g32p_row26_traceSegment_044_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 468 9 9, g32p_row26_traceSegment_044_0468_0009, g32p_row26_traceSegment_044_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 486 9 9, g32p_row26_traceSegment_044_0486_0009, g32p_row26_traceSegment_044_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 468 18 18, g32p_row26_traceSegment_044_0468_0018, g32p_row26_traceSegment_044_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 432 36 36, g32p_row26_traceSegment_044_0432_0036, g32p_row26_traceSegment_044_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 504 9 9, g32p_row26_traceSegment_044_0504_0009, g32p_row26_traceSegment_044_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 522 9 9, g32p_row26_traceSegment_044_0522_0009, g32p_row26_traceSegment_044_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 504 18 18, g32p_row26_traceSegment_044_0504_0018, g32p_row26_traceSegment_044_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 540 9 9, g32p_row26_traceSegment_044_0540_0009, g32p_row26_traceSegment_044_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_044 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_044_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_044 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 558 9 9, g32p_row26_traceSegment_044_0558_0009, g32p_row26_traceSegment_044_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_044 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 540 18 18, g32p_row26_traceSegment_044_0540_0018, g32p_row26_traceSegment_044_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_044 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 504 36 36, g32p_row26_traceSegment_044_0504_0036, g32p_row26_traceSegment_044_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_044 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 432 72 72, g32p_row26_traceSegment_044_0432_0072, g32p_row26_traceSegment_044_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_044 288 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 288 144 144, g32p_row26_traceSegment_044_0288_0144, g32p_row26_traceSegment_044_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_044_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_044 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_044 0 288 288, g32p_row26_traceSegment_044_0000_0288, g32p_row26_traceSegment_044_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 44 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_044_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_048 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 48 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_048_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 0 9 9, g32p_row26_traceSegment_048_0000_0009, g32p_row26_traceSegment_048_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 18 9 9, g32p_row26_traceSegment_048_0018_0009, g32p_row26_traceSegment_048_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 0 18 18, g32p_row26_traceSegment_048_0000_0018, g32p_row26_traceSegment_048_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 36 9 9, g32p_row26_traceSegment_048_0036_0009, g32p_row26_traceSegment_048_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 54 9 9, g32p_row26_traceSegment_048_0054_0009, g32p_row26_traceSegment_048_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 36 18 18, g32p_row26_traceSegment_048_0036_0018, g32p_row26_traceSegment_048_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 0 36 36, g32p_row26_traceSegment_048_0000_0036, g32p_row26_traceSegment_048_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 72 9 9, g32p_row26_traceSegment_048_0072_0009, g32p_row26_traceSegment_048_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 90 9 9, g32p_row26_traceSegment_048_0090_0009, g32p_row26_traceSegment_048_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 72 18 18, g32p_row26_traceSegment_048_0072_0018, g32p_row26_traceSegment_048_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 108 9 9, g32p_row26_traceSegment_048_0108_0009, g32p_row26_traceSegment_048_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 126 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 126 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 126 9 9, g32p_row26_traceSegment_048_0126_0009, g32p_row26_traceSegment_048_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 108 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 108 18 18, g32p_row26_traceSegment_048_0108_0018, g32p_row26_traceSegment_048_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 72 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 72 36 36, g32p_row26_traceSegment_048_0072_0036, g32p_row26_traceSegment_048_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_048 0 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 0 72 72, g32p_row26_traceSegment_048_0000_0072, g32p_row26_traceSegment_048_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 144 9 9, g32p_row26_traceSegment_048_0144_0009, g32p_row26_traceSegment_048_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 162 9 9, g32p_row26_traceSegment_048_0162_0009, g32p_row26_traceSegment_048_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 144 18 18, g32p_row26_traceSegment_048_0144_0018, g32p_row26_traceSegment_048_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 180 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 180 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 180 9 9, g32p_row26_traceSegment_048_0180_0009, g32p_row26_traceSegment_048_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 198 9 9, g32p_row26_traceSegment_048_0198_0009, g32p_row26_traceSegment_048_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 180 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 180 18 18, g32p_row26_traceSegment_048_0180_0018, g32p_row26_traceSegment_048_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 144 72 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 144 36 36, g32p_row26_traceSegment_048_0144_0036, g32p_row26_traceSegment_048_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 225 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 216 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 216 9 9, g32p_row26_traceSegment_048_0216_0009, g32p_row26_traceSegment_048_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 234 9 = [0, 2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 234 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 234 9 9, g32p_row26_traceSegment_048_0234_0009, g32p_row26_traceSegment_048_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 216 36 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 216 18 18, g32p_row26_traceSegment_048_0216_0018, g32p_row26_traceSegment_048_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 252 9 9, g32p_row26_traceSegment_048_0252_0009, g32p_row26_traceSegment_048_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 270 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 270 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 270 9 9, g32p_row26_traceSegment_048_0270_0009, g32p_row26_traceSegment_048_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 252 18 18, g32p_row26_traceSegment_048_0252_0018, g32p_row26_traceSegment_048_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 216 72 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 216 36 36, g32p_row26_traceSegment_048_0216_0036, g32p_row26_traceSegment_048_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_048 144 144 = [0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 144 72 72, g32p_row26_traceSegment_048_0144_0072, g32p_row26_traceSegment_048_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_048 0 288 = [0, 5, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 0 144 144, g32p_row26_traceSegment_048_0000_0144, g32p_row26_traceSegment_048_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 288 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 297 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 288 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 288 9 9, g32p_row26_traceSegment_048_0288_0009, g32p_row26_traceSegment_048_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 306 9 9, g32p_row26_traceSegment_048_0306_0009, g32p_row26_traceSegment_048_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 288 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 288 18 18, g32p_row26_traceSegment_048_0288_0018, g32p_row26_traceSegment_048_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 324 9 9, g32p_row26_traceSegment_048_0324_0009, g32p_row26_traceSegment_048_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 342 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 351 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 342 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 342 9 9, g32p_row26_traceSegment_048_0342_0009, g32p_row26_traceSegment_048_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 324 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 324 18 18, g32p_row26_traceSegment_048_0324_0018, g32p_row26_traceSegment_048_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 288 72 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 288 36 36, g32p_row26_traceSegment_048_0288_0036, g32p_row26_traceSegment_048_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 360 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 360 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 360 9 9, g32p_row26_traceSegment_048_0360_0009, g32p_row26_traceSegment_048_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 378 9 9, g32p_row26_traceSegment_048_0378_0009, g32p_row26_traceSegment_048_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 360 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 360 18 18, g32p_row26_traceSegment_048_0360_0018, g32p_row26_traceSegment_048_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 396 9 9, g32p_row26_traceSegment_048_0396_0009, g32p_row26_traceSegment_048_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 414 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 414 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 414 9 9, g32p_row26_traceSegment_048_0414_0009, g32p_row26_traceSegment_048_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 396 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 396 18 18, g32p_row26_traceSegment_048_0396_0018, g32p_row26_traceSegment_048_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 360 72 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 360 36 36, g32p_row26_traceSegment_048_0360_0036, g32p_row26_traceSegment_048_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_048 288 144 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 288 72 72, g32p_row26_traceSegment_048_0288_0072, g32p_row26_traceSegment_048_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 432 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 432 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 432 9 9, g32p_row26_traceSegment_048_0432_0009, g32p_row26_traceSegment_048_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 450 9 9, g32p_row26_traceSegment_048_0450_0009, g32p_row26_traceSegment_048_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 432 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 432 18 18, g32p_row26_traceSegment_048_0432_0018, g32p_row26_traceSegment_048_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 468 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 468 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 468 9 9, g32p_row26_traceSegment_048_0468_0009, g32p_row26_traceSegment_048_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 486 9 9, g32p_row26_traceSegment_048_0486_0009, g32p_row26_traceSegment_048_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 468 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 468 18 18, g32p_row26_traceSegment_048_0468_0018, g32p_row26_traceSegment_048_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 432 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 432 36 36, g32p_row26_traceSegment_048_0432_0036, g32p_row26_traceSegment_048_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 504 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 504 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 504 9 9, g32p_row26_traceSegment_048_0504_0009, g32p_row26_traceSegment_048_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 531 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 522 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 522 9 9, g32p_row26_traceSegment_048_0522_0009, g32p_row26_traceSegment_048_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 504 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 504 18 18, g32p_row26_traceSegment_048_0504_0018, g32p_row26_traceSegment_048_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 540 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 549 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 540 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 540 9 9, g32p_row26_traceSegment_048_0540_0009, g32p_row26_traceSegment_048_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_048 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_048_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_048 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 558 9 9, g32p_row26_traceSegment_048_0558_0009, g32p_row26_traceSegment_048_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_048 540 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 540 18 18, g32p_row26_traceSegment_048_0540_0018, g32p_row26_traceSegment_048_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_048 504 72 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 504 36 36, g32p_row26_traceSegment_048_0504_0036, g32p_row26_traceSegment_048_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_048 432 144 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 432 72 72, g32p_row26_traceSegment_048_0432_0072, g32p_row26_traceSegment_048_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_048 288 288 = [0, 11, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 288 144 144, g32p_row26_traceSegment_048_0288_0144, g32p_row26_traceSegment_048_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_048_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_048 0 576 = [0, 16, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_048 0 288 288, g32p_row26_traceSegment_048_0000_0288, g32p_row26_traceSegment_048_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 48 = [0, 16, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_048_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_051 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 51 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_051_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 0 9 9, g32p_row26_traceSegment_051_0000_0009, g32p_row26_traceSegment_051_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 18 9 9, g32p_row26_traceSegment_051_0018_0009, g32p_row26_traceSegment_051_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 0 18 18, g32p_row26_traceSegment_051_0000_0018, g32p_row26_traceSegment_051_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 36 9 = [2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 36 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 36 9 9, g32p_row26_traceSegment_051_0036_0009, g32p_row26_traceSegment_051_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 54 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 54 9 9, g32p_row26_traceSegment_051_0054_0009, g32p_row26_traceSegment_051_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 36 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 36 18 18, g32p_row26_traceSegment_051_0036_0018, g32p_row26_traceSegment_051_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 0 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 0 36 36, g32p_row26_traceSegment_051_0000_0036, g32p_row26_traceSegment_051_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 72 9 9, g32p_row26_traceSegment_051_0072_0009, g32p_row26_traceSegment_051_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 90 9 9, g32p_row26_traceSegment_051_0090_0009, g32p_row26_traceSegment_051_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 72 18 18, g32p_row26_traceSegment_051_0072_0018, g32p_row26_traceSegment_051_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 108 9 9, g32p_row26_traceSegment_051_0108_0009, g32p_row26_traceSegment_051_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 126 9 9, g32p_row26_traceSegment_051_0126_0009, g32p_row26_traceSegment_051_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 108 18 18, g32p_row26_traceSegment_051_0108_0018, g32p_row26_traceSegment_051_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 72 36 36, g32p_row26_traceSegment_051_0072_0036, g32p_row26_traceSegment_051_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_051 0 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 0 72 72, g32p_row26_traceSegment_051_0000_0072, g32p_row26_traceSegment_051_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 144 9 9, g32p_row26_traceSegment_051_0144_0009, g32p_row26_traceSegment_051_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 162 9 9, g32p_row26_traceSegment_051_0162_0009, g32p_row26_traceSegment_051_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 144 18 18, g32p_row26_traceSegment_051_0144_0018, g32p_row26_traceSegment_051_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 180 9 9, g32p_row26_traceSegment_051_0180_0009, g32p_row26_traceSegment_051_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 198 9 9, g32p_row26_traceSegment_051_0198_0009, g32p_row26_traceSegment_051_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 180 18 18, g32p_row26_traceSegment_051_0180_0018, g32p_row26_traceSegment_051_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 144 36 36, g32p_row26_traceSegment_051_0144_0036, g32p_row26_traceSegment_051_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 216 9 9, g32p_row26_traceSegment_051_0216_0009, g32p_row26_traceSegment_051_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 234 9 9, g32p_row26_traceSegment_051_0234_0009, g32p_row26_traceSegment_051_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 216 18 18, g32p_row26_traceSegment_051_0216_0018, g32p_row26_traceSegment_051_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 252 9 9, g32p_row26_traceSegment_051_0252_0009, g32p_row26_traceSegment_051_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 270 9 9, g32p_row26_traceSegment_051_0270_0009, g32p_row26_traceSegment_051_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 252 18 18, g32p_row26_traceSegment_051_0252_0018, g32p_row26_traceSegment_051_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 216 36 36, g32p_row26_traceSegment_051_0216_0036, g32p_row26_traceSegment_051_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_051 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 144 72 72, g32p_row26_traceSegment_051_0144_0072, g32p_row26_traceSegment_051_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_051 0 288 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 0 144 144, g32p_row26_traceSegment_051_0000_0144, g32p_row26_traceSegment_051_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 288 9 9, g32p_row26_traceSegment_051_0288_0009, g32p_row26_traceSegment_051_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 306 9 9, g32p_row26_traceSegment_051_0306_0009, g32p_row26_traceSegment_051_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 288 18 18, g32p_row26_traceSegment_051_0288_0018, g32p_row26_traceSegment_051_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 324 9 9, g32p_row26_traceSegment_051_0324_0009, g32p_row26_traceSegment_051_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 342 9 9, g32p_row26_traceSegment_051_0342_0009, g32p_row26_traceSegment_051_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 324 18 18, g32p_row26_traceSegment_051_0324_0018, g32p_row26_traceSegment_051_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 288 36 36, g32p_row26_traceSegment_051_0288_0036, g32p_row26_traceSegment_051_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 360 9 9, g32p_row26_traceSegment_051_0360_0009, g32p_row26_traceSegment_051_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 378 9 9, g32p_row26_traceSegment_051_0378_0009, g32p_row26_traceSegment_051_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 360 18 18, g32p_row26_traceSegment_051_0360_0018, g32p_row26_traceSegment_051_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 405 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 396 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 396 9 9, g32p_row26_traceSegment_051_0396_0009, g32p_row26_traceSegment_051_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 414 9 9, g32p_row26_traceSegment_051_0414_0009, g32p_row26_traceSegment_051_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 396 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 396 18 18, g32p_row26_traceSegment_051_0396_0018, g32p_row26_traceSegment_051_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 360 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 360 36 36, g32p_row26_traceSegment_051_0360_0036, g32p_row26_traceSegment_051_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_051 288 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 288 72 72, g32p_row26_traceSegment_051_0288_0072, g32p_row26_traceSegment_051_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 432 9 9, g32p_row26_traceSegment_051_0432_0009, g32p_row26_traceSegment_051_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 450 9 9, g32p_row26_traceSegment_051_0450_0009, g32p_row26_traceSegment_051_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 432 18 18, g32p_row26_traceSegment_051_0432_0018, g32p_row26_traceSegment_051_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 468 9 9, g32p_row26_traceSegment_051_0468_0009, g32p_row26_traceSegment_051_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 486 9 9, g32p_row26_traceSegment_051_0486_0009, g32p_row26_traceSegment_051_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 468 18 18, g32p_row26_traceSegment_051_0468_0018, g32p_row26_traceSegment_051_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 432 36 36, g32p_row26_traceSegment_051_0432_0036, g32p_row26_traceSegment_051_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 504 9 9, g32p_row26_traceSegment_051_0504_0009, g32p_row26_traceSegment_051_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 522 9 9, g32p_row26_traceSegment_051_0522_0009, g32p_row26_traceSegment_051_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 504 18 18, g32p_row26_traceSegment_051_0504_0018, g32p_row26_traceSegment_051_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 540 9 9, g32p_row26_traceSegment_051_0540_0009, g32p_row26_traceSegment_051_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_051 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_051_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_051 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 558 9 9, g32p_row26_traceSegment_051_0558_0009, g32p_row26_traceSegment_051_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_051 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 540 18 18, g32p_row26_traceSegment_051_0540_0018, g32p_row26_traceSegment_051_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_051 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 504 36 36, g32p_row26_traceSegment_051_0504_0036, g32p_row26_traceSegment_051_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_051 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 432 72 72, g32p_row26_traceSegment_051_0432_0072, g32p_row26_traceSegment_051_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_051 288 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 288 144 144, g32p_row26_traceSegment_051_0288_0144, g32p_row26_traceSegment_051_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_051_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_051 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_051 0 288 288, g32p_row26_traceSegment_051_0000_0288, g32p_row26_traceSegment_051_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 51 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_051_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_052 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 52 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_052_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 9 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 0 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 0 9 9, g32p_row26_traceSegment_052_0000_0009, g32p_row26_traceSegment_052_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 18 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 18 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 18 9 9, g32p_row26_traceSegment_052_0018_0009, g32p_row26_traceSegment_052_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 0 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 0 18 18, g32p_row26_traceSegment_052_0000_0018, g32p_row26_traceSegment_052_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 36 9 9, g32p_row26_traceSegment_052_0036_0009, g32p_row26_traceSegment_052_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 54 9 9, g32p_row26_traceSegment_052_0054_0009, g32p_row26_traceSegment_052_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 36 18 18, g32p_row26_traceSegment_052_0036_0018, g32p_row26_traceSegment_052_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 0 72 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 0 36 36, g32p_row26_traceSegment_052_0000_0036, g32p_row26_traceSegment_052_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 72 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 72 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 72 9 9, g32p_row26_traceSegment_052_0072_0009, g32p_row26_traceSegment_052_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 90 9 9, g32p_row26_traceSegment_052_0090_0009, g32p_row26_traceSegment_052_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 72 18 18, g32p_row26_traceSegment_052_0072_0018, g32p_row26_traceSegment_052_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 108 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 108 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 108 9 9, g32p_row26_traceSegment_052_0108_0009, g32p_row26_traceSegment_052_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 135 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 126 9 9, g32p_row26_traceSegment_052_0126_0009, g32p_row26_traceSegment_052_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 108 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 108 18 18, g32p_row26_traceSegment_052_0108_0018, g32p_row26_traceSegment_052_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 72 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 72 36 36, g32p_row26_traceSegment_052_0072_0036, g32p_row26_traceSegment_052_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_052 0 144 = [0, 0, 4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 0 72 72, g32p_row26_traceSegment_052_0000_0072, g32p_row26_traceSegment_052_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 153 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 144 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 144 9 9, g32p_row26_traceSegment_052_0144_0009, g32p_row26_traceSegment_052_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 162 9 9, g32p_row26_traceSegment_052_0162_0009, g32p_row26_traceSegment_052_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 144 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 144 18 18, g32p_row26_traceSegment_052_0144_0018, g32p_row26_traceSegment_052_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 180 9 9, g32p_row26_traceSegment_052_0180_0009, g32p_row26_traceSegment_052_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 198 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 198 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 198 9 9, g32p_row26_traceSegment_052_0198_0009, g32p_row26_traceSegment_052_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 180 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 180 18 18, g32p_row26_traceSegment_052_0180_0018, g32p_row26_traceSegment_052_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 144 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 144 36 36, g32p_row26_traceSegment_052_0144_0036, g32p_row26_traceSegment_052_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 216 9 9, g32p_row26_traceSegment_052_0216_0009, g32p_row26_traceSegment_052_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 234 9 9, g32p_row26_traceSegment_052_0234_0009, g32p_row26_traceSegment_052_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 216 18 18, g32p_row26_traceSegment_052_0216_0018, g32p_row26_traceSegment_052_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 252 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 252 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 252 9 9, g32p_row26_traceSegment_052_0252_0009, g32p_row26_traceSegment_052_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 270 9 9, g32p_row26_traceSegment_052_0270_0009, g32p_row26_traceSegment_052_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 252 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 252 18 18, g32p_row26_traceSegment_052_0252_0018, g32p_row26_traceSegment_052_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 216 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 216 36 36, g32p_row26_traceSegment_052_0216_0036, g32p_row26_traceSegment_052_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_052 144 144 = [0, 0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 144 72 72, g32p_row26_traceSegment_052_0144_0072, g32p_row26_traceSegment_052_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_052 0 288 = [0, 0, 8, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 0 144 144, g32p_row26_traceSegment_052_0000_0144, g32p_row26_traceSegment_052_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 288 9 9, g32p_row26_traceSegment_052_0288_0009, g32p_row26_traceSegment_052_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 306 9 9, g32p_row26_traceSegment_052_0306_0009, g32p_row26_traceSegment_052_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 288 18 18, g32p_row26_traceSegment_052_0288_0018, g32p_row26_traceSegment_052_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 324 9 9, g32p_row26_traceSegment_052_0324_0009, g32p_row26_traceSegment_052_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 342 9 9, g32p_row26_traceSegment_052_0342_0009, g32p_row26_traceSegment_052_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 324 18 18, g32p_row26_traceSegment_052_0324_0018, g32p_row26_traceSegment_052_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 288 36 36, g32p_row26_traceSegment_052_0288_0036, g32p_row26_traceSegment_052_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 360 9 9, g32p_row26_traceSegment_052_0360_0009, g32p_row26_traceSegment_052_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 378 9 9, g32p_row26_traceSegment_052_0378_0009, g32p_row26_traceSegment_052_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 360 18 18, g32p_row26_traceSegment_052_0360_0018, g32p_row26_traceSegment_052_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 396 9 9, g32p_row26_traceSegment_052_0396_0009, g32p_row26_traceSegment_052_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 414 9 9, g32p_row26_traceSegment_052_0414_0009, g32p_row26_traceSegment_052_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 396 18 18, g32p_row26_traceSegment_052_0396_0018, g32p_row26_traceSegment_052_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 360 36 36, g32p_row26_traceSegment_052_0360_0036, g32p_row26_traceSegment_052_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_052 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 288 72 72, g32p_row26_traceSegment_052_0288_0072, g32p_row26_traceSegment_052_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 432 9 9, g32p_row26_traceSegment_052_0432_0009, g32p_row26_traceSegment_052_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 450 9 9, g32p_row26_traceSegment_052_0450_0009, g32p_row26_traceSegment_052_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 432 18 18, g32p_row26_traceSegment_052_0432_0018, g32p_row26_traceSegment_052_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 468 9 9, g32p_row26_traceSegment_052_0468_0009, g32p_row26_traceSegment_052_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 486 9 9, g32p_row26_traceSegment_052_0486_0009, g32p_row26_traceSegment_052_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 468 18 18, g32p_row26_traceSegment_052_0468_0018, g32p_row26_traceSegment_052_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 432 36 36, g32p_row26_traceSegment_052_0432_0036, g32p_row26_traceSegment_052_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 504 9 9, g32p_row26_traceSegment_052_0504_0009, g32p_row26_traceSegment_052_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 522 9 9, g32p_row26_traceSegment_052_0522_0009, g32p_row26_traceSegment_052_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 504 18 18, g32p_row26_traceSegment_052_0504_0018, g32p_row26_traceSegment_052_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 540 9 9, g32p_row26_traceSegment_052_0540_0009, g32p_row26_traceSegment_052_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_052 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_052_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_052 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 558 9 9, g32p_row26_traceSegment_052_0558_0009, g32p_row26_traceSegment_052_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_052 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 540 18 18, g32p_row26_traceSegment_052_0540_0018, g32p_row26_traceSegment_052_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_052 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 504 36 36, g32p_row26_traceSegment_052_0504_0036, g32p_row26_traceSegment_052_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_052 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 432 72 72, g32p_row26_traceSegment_052_0432_0072, g32p_row26_traceSegment_052_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_052 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 288 144 144, g32p_row26_traceSegment_052_0288_0144, g32p_row26_traceSegment_052_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_052_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_052 0 576 = [0, 0, 8, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_052 0 288 288, g32p_row26_traceSegment_052_0000_0288, g32p_row26_traceSegment_052_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 52 = [0, 0, 8, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_052_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_055 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 55 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_055_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 0 9 9, g32p_row26_traceSegment_055_0000_0009, g32p_row26_traceSegment_055_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 27 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 18 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 18 9 9, g32p_row26_traceSegment_055_0018_0009, g32p_row26_traceSegment_055_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 0 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 0 18 18, g32p_row26_traceSegment_055_0000_0018, g32p_row26_traceSegment_055_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 36 9 9, g32p_row26_traceSegment_055_0036_0009, g32p_row26_traceSegment_055_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 54 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 63 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 54 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 54 9 9, g32p_row26_traceSegment_055_0054_0009, g32p_row26_traceSegment_055_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 36 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 36 18 18, g32p_row26_traceSegment_055_0036_0018, g32p_row26_traceSegment_055_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 0 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 0 36 36, g32p_row26_traceSegment_055_0000_0036, g32p_row26_traceSegment_055_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 81 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 72 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 72 9 9, g32p_row26_traceSegment_055_0072_0009, g32p_row26_traceSegment_055_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 90 9 9, g32p_row26_traceSegment_055_0090_0009, g32p_row26_traceSegment_055_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 72 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 72 18 18, g32p_row26_traceSegment_055_0072_0018, g32p_row26_traceSegment_055_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 108 9 9, g32p_row26_traceSegment_055_0108_0009, g32p_row26_traceSegment_055_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 126 9 9, g32p_row26_traceSegment_055_0126_0009, g32p_row26_traceSegment_055_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 108 18 18, g32p_row26_traceSegment_055_0108_0018, g32p_row26_traceSegment_055_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 72 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 72 36 36, g32p_row26_traceSegment_055_0072_0036, g32p_row26_traceSegment_055_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_055 0 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 0 72 72, g32p_row26_traceSegment_055_0000_0072, g32p_row26_traceSegment_055_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 144 9 9, g32p_row26_traceSegment_055_0144_0009, g32p_row26_traceSegment_055_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 162 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 162 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 162 9 9, g32p_row26_traceSegment_055_0162_0009, g32p_row26_traceSegment_055_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 144 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 144 18 18, g32p_row26_traceSegment_055_0144_0018, g32p_row26_traceSegment_055_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 189 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 180 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 180 9 9, g32p_row26_traceSegment_055_0180_0009, g32p_row26_traceSegment_055_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 207 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 198 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 198 9 9, g32p_row26_traceSegment_055_0198_0009, g32p_row26_traceSegment_055_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 180 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 180 18 18, g32p_row26_traceSegment_055_0180_0018, g32p_row26_traceSegment_055_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 144 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 144 36 36, g32p_row26_traceSegment_055_0144_0036, g32p_row26_traceSegment_055_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 216 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 216 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 216 9 9, g32p_row26_traceSegment_055_0216_0009, g32p_row26_traceSegment_055_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 234 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 234 9 9, g32p_row26_traceSegment_055_0234_0009, g32p_row26_traceSegment_055_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 216 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 216 18 18, g32p_row26_traceSegment_055_0216_0018, g32p_row26_traceSegment_055_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 252 9 9, g32p_row26_traceSegment_055_0252_0009, g32p_row26_traceSegment_055_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 279 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 270 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 270 9 9, g32p_row26_traceSegment_055_0270_0009, g32p_row26_traceSegment_055_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 252 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 252 18 18, g32p_row26_traceSegment_055_0252_0018, g32p_row26_traceSegment_055_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 216 72 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 216 36 36, g32p_row26_traceSegment_055_0216_0036, g32p_row26_traceSegment_055_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_055 144 144 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 144 72 72, g32p_row26_traceSegment_055_0144_0072, g32p_row26_traceSegment_055_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_055 0 288 = [1, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 0 144 144, g32p_row26_traceSegment_055_0000_0144, g32p_row26_traceSegment_055_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 288 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 288 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 288 9 9, g32p_row26_traceSegment_055_0288_0009, g32p_row26_traceSegment_055_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 315 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 306 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 306 9 9, g32p_row26_traceSegment_055_0306_0009, g32p_row26_traceSegment_055_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 288 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 288 18 18, g32p_row26_traceSegment_055_0288_0018, g32p_row26_traceSegment_055_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 324 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 333 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 324 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 324 9 9, g32p_row26_traceSegment_055_0324_0009, g32p_row26_traceSegment_055_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 342 9 9, g32p_row26_traceSegment_055_0342_0009, g32p_row26_traceSegment_055_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 324 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 324 18 18, g32p_row26_traceSegment_055_0324_0018, g32p_row26_traceSegment_055_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 288 72 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 288 36 36, g32p_row26_traceSegment_055_0288_0036, g32p_row26_traceSegment_055_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 360 9 9, g32p_row26_traceSegment_055_0360_0009, g32p_row26_traceSegment_055_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 378 9 9, g32p_row26_traceSegment_055_0378_0009, g32p_row26_traceSegment_055_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 360 18 18, g32p_row26_traceSegment_055_0360_0018, g32p_row26_traceSegment_055_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 396 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 405 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 396 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 396 9 9, g32p_row26_traceSegment_055_0396_0009, g32p_row26_traceSegment_055_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 423 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 414 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 414 9 9, g32p_row26_traceSegment_055_0414_0009, g32p_row26_traceSegment_055_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 396 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 396 18 18, g32p_row26_traceSegment_055_0396_0018, g32p_row26_traceSegment_055_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 360 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 360 36 36, g32p_row26_traceSegment_055_0360_0036, g32p_row26_traceSegment_055_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_055 288 144 = [3, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 288 72 72, g32p_row26_traceSegment_055_0288_0072, g32p_row26_traceSegment_055_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 432 9 9, g32p_row26_traceSegment_055_0432_0009, g32p_row26_traceSegment_055_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 459 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 450 9 9, g32p_row26_traceSegment_055_0450_0009, g32p_row26_traceSegment_055_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 432 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 432 18 18, g32p_row26_traceSegment_055_0432_0018, g32p_row26_traceSegment_055_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 468 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 468 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 468 9 9, g32p_row26_traceSegment_055_0468_0009, g32p_row26_traceSegment_055_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 495 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 486 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 486 9 9, g32p_row26_traceSegment_055_0486_0009, g32p_row26_traceSegment_055_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 468 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 468 18 18, g32p_row26_traceSegment_055_0468_0018, g32p_row26_traceSegment_055_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 432 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 432 36 36, g32p_row26_traceSegment_055_0432_0036, g32p_row26_traceSegment_055_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 504 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 504 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 504 9 9, g32p_row26_traceSegment_055_0504_0009, g32p_row26_traceSegment_055_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 522 9 9, g32p_row26_traceSegment_055_0522_0009, g32p_row26_traceSegment_055_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 504 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 504 18 18, g32p_row26_traceSegment_055_0504_0018, g32p_row26_traceSegment_055_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 540 9 9, g32p_row26_traceSegment_055_0540_0009, g32p_row26_traceSegment_055_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_055 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_055_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_055 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 558 9 9, g32p_row26_traceSegment_055_0558_0009, g32p_row26_traceSegment_055_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_055 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 540 18 18, g32p_row26_traceSegment_055_0540_0018, g32p_row26_traceSegment_055_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_055 504 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 504 36 36, g32p_row26_traceSegment_055_0504_0036, g32p_row26_traceSegment_055_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_055 432 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 432 72 72, g32p_row26_traceSegment_055_0432_0072, g32p_row26_traceSegment_055_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_055 288 288 = [7, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 288 144 144, g32p_row26_traceSegment_055_0288_0144, g32p_row26_traceSegment_055_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_055_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_055 0 576 = [8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_055 0 288 288, g32p_row26_traceSegment_055_0000_0288, g32p_row26_traceSegment_055_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 55 = [8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_055_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 34) (g32p_literalTraceValue 25 34)
      [1, -1, 1] [-3456, 3456, 3456] = true := by
  rw [g32p_row26_traceCoefficients_034]
  decide +kernel

theorem g32p_row26_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 37) (g32p_literalTraceValue 25 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row26_traceCoefficients_037]
  decide +kernel

theorem g32p_row26_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 41) (g32p_literalTraceValue 25 41)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_041]
  decide +kernel

theorem g32p_row26_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 44) (g32p_literalTraceValue 25 44)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_044]
  decide +kernel

theorem g32p_row26_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 48) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 48) (g32p_literalTraceValue 25 48)
      [1, -1, 1] [-576, 576, 576] = true := by
  rw [g32p_row26_traceCoefficients_048]
  decide +kernel

theorem g32p_row26_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 51) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 51) (g32p_literalTraceValue 25 51)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_051]
  decide +kernel

theorem g32p_row26_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 52) (g32p_literalTraceValue 25 52)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_052]
  decide +kernel

theorem g32p_row26_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 55) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 55) (g32p_literalTraceValue 25 55)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_055]
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

private def g32p_row26_traceSegment_058 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 58 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_058_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 0 9 9, g32p_row26_traceSegment_058_0000_0009, g32p_row26_traceSegment_058_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 27 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 18 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 18 9 9, g32p_row26_traceSegment_058_0018_0009, g32p_row26_traceSegment_058_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 0 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 0 18 18, g32p_row26_traceSegment_058_0000_0018, g32p_row26_traceSegment_058_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 45 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 36 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 36 9 9, g32p_row26_traceSegment_058_0036_0009, g32p_row26_traceSegment_058_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 54 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 54 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 54 9 9, g32p_row26_traceSegment_058_0054_0009, g32p_row26_traceSegment_058_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 36 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 36 18 18, g32p_row26_traceSegment_058_0036_0018, g32p_row26_traceSegment_058_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 0 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 0 36 36, g32p_row26_traceSegment_058_0000_0036, g32p_row26_traceSegment_058_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 72 9 9, g32p_row26_traceSegment_058_0072_0009, g32p_row26_traceSegment_058_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 90 9 9, g32p_row26_traceSegment_058_0090_0009, g32p_row26_traceSegment_058_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 72 18 18, g32p_row26_traceSegment_058_0072_0018, g32p_row26_traceSegment_058_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 108 9 9, g32p_row26_traceSegment_058_0108_0009, g32p_row26_traceSegment_058_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 126 9 9, g32p_row26_traceSegment_058_0126_0009, g32p_row26_traceSegment_058_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 108 18 18, g32p_row26_traceSegment_058_0108_0018, g32p_row26_traceSegment_058_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 72 36 36, g32p_row26_traceSegment_058_0072_0036, g32p_row26_traceSegment_058_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_058 0 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 0 72 72, g32p_row26_traceSegment_058_0000_0072, g32p_row26_traceSegment_058_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 144 9 9, g32p_row26_traceSegment_058_0144_0009, g32p_row26_traceSegment_058_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 162 9 9, g32p_row26_traceSegment_058_0162_0009, g32p_row26_traceSegment_058_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 144 18 18, g32p_row26_traceSegment_058_0144_0018, g32p_row26_traceSegment_058_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 180 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 189 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 180 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 180 9 9, g32p_row26_traceSegment_058_0180_0009, g32p_row26_traceSegment_058_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 207 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 198 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 198 9 9, g32p_row26_traceSegment_058_0198_0009, g32p_row26_traceSegment_058_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 180 36 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 180 18 18, g32p_row26_traceSegment_058_0180_0018, g32p_row26_traceSegment_058_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 144 72 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 144 36 36, g32p_row26_traceSegment_058_0144_0036, g32p_row26_traceSegment_058_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 225 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 216 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 216 9 9, g32p_row26_traceSegment_058_0216_0009, g32p_row26_traceSegment_058_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 234 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 243 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 234 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 234 9 9, g32p_row26_traceSegment_058_0234_0009, g32p_row26_traceSegment_058_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 216 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 216 18 18, g32p_row26_traceSegment_058_0216_0018, g32p_row26_traceSegment_058_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 252 9 9, g32p_row26_traceSegment_058_0252_0009, g32p_row26_traceSegment_058_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 270 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 270 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 270 9 9, g32p_row26_traceSegment_058_0270_0009, g32p_row26_traceSegment_058_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 252 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 252 18 18, g32p_row26_traceSegment_058_0252_0018, g32p_row26_traceSegment_058_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 216 72 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 216 36 36, g32p_row26_traceSegment_058_0216_0036, g32p_row26_traceSegment_058_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_058 144 144 = [0, 0, 6, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 144 72 72, g32p_row26_traceSegment_058_0144_0072, g32p_row26_traceSegment_058_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_058 0 288 = [0, 0, 6, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 0 144 144, g32p_row26_traceSegment_058_0000_0144, g32p_row26_traceSegment_058_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 297 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 288 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 288 9 9, g32p_row26_traceSegment_058_0288_0009, g32p_row26_traceSegment_058_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 315 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 306 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 306 9 9, g32p_row26_traceSegment_058_0306_0009, g32p_row26_traceSegment_058_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 288 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 288 18 18, g32p_row26_traceSegment_058_0288_0018, g32p_row26_traceSegment_058_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 324 9 9, g32p_row26_traceSegment_058_0324_0009, g32p_row26_traceSegment_058_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 342 9 9, g32p_row26_traceSegment_058_0342_0009, g32p_row26_traceSegment_058_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 324 18 18, g32p_row26_traceSegment_058_0324_0018, g32p_row26_traceSegment_058_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 288 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 288 36 36, g32p_row26_traceSegment_058_0288_0036, g32p_row26_traceSegment_058_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 360 9 9, g32p_row26_traceSegment_058_0360_0009, g32p_row26_traceSegment_058_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 378 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 378 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 378 9 9, g32p_row26_traceSegment_058_0378_0009, g32p_row26_traceSegment_058_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 360 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 360 18 18, g32p_row26_traceSegment_058_0360_0018, g32p_row26_traceSegment_058_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 405 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 396 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 396 9 9, g32p_row26_traceSegment_058_0396_0009, g32p_row26_traceSegment_058_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 414 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 423 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 414 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 414 9 9, g32p_row26_traceSegment_058_0414_0009, g32p_row26_traceSegment_058_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 396 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 396 18 18, g32p_row26_traceSegment_058_0396_0018, g32p_row26_traceSegment_058_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 360 72 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 360 36 36, g32p_row26_traceSegment_058_0360_0036, g32p_row26_traceSegment_058_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_058 288 144 = [0, 0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 288 72 72, g32p_row26_traceSegment_058_0288_0072, g32p_row26_traceSegment_058_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 432 9 9, g32p_row26_traceSegment_058_0432_0009, g32p_row26_traceSegment_058_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 459 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 450 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 450 9 9, g32p_row26_traceSegment_058_0450_0009, g32p_row26_traceSegment_058_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 432 18 18, g32p_row26_traceSegment_058_0432_0018, g32p_row26_traceSegment_058_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 468 9 9, g32p_row26_traceSegment_058_0468_0009, g32p_row26_traceSegment_058_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 495 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 486 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 486 9 9, g32p_row26_traceSegment_058_0486_0009, g32p_row26_traceSegment_058_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 468 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 468 18 18, g32p_row26_traceSegment_058_0468_0018, g32p_row26_traceSegment_058_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 432 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 432 36 36, g32p_row26_traceSegment_058_0432_0036, g32p_row26_traceSegment_058_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 504 9 9, g32p_row26_traceSegment_058_0504_0009, g32p_row26_traceSegment_058_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 522 9 9, g32p_row26_traceSegment_058_0522_0009, g32p_row26_traceSegment_058_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 504 18 18, g32p_row26_traceSegment_058_0504_0018, g32p_row26_traceSegment_058_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 540 9 9, g32p_row26_traceSegment_058_0540_0009, g32p_row26_traceSegment_058_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_058 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_058_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_058 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 558 9 9, g32p_row26_traceSegment_058_0558_0009, g32p_row26_traceSegment_058_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_058 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 540 18 18, g32p_row26_traceSegment_058_0540_0018, g32p_row26_traceSegment_058_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_058 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 504 36 36, g32p_row26_traceSegment_058_0504_0036, g32p_row26_traceSegment_058_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_058 432 144 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 432 72 72, g32p_row26_traceSegment_058_0432_0072, g32p_row26_traceSegment_058_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_058 288 288 = [0, 0, 2, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 288 144 144, g32p_row26_traceSegment_058_0288_0144, g32p_row26_traceSegment_058_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_058_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_058 0 576 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_058 0 288 288, g32p_row26_traceSegment_058_0000_0288, g32p_row26_traceSegment_058_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 58 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_058_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_061 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 61 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_061_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 0 9 9, g32p_row26_traceSegment_061_0000_0009, g32p_row26_traceSegment_061_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 18 9 9, g32p_row26_traceSegment_061_0018_0009, g32p_row26_traceSegment_061_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 0 18 18, g32p_row26_traceSegment_061_0000_0018, g32p_row26_traceSegment_061_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 36 9 9, g32p_row26_traceSegment_061_0036_0009, g32p_row26_traceSegment_061_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 54 9 9, g32p_row26_traceSegment_061_0054_0009, g32p_row26_traceSegment_061_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 36 18 18, g32p_row26_traceSegment_061_0036_0018, g32p_row26_traceSegment_061_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 0 36 36, g32p_row26_traceSegment_061_0000_0036, g32p_row26_traceSegment_061_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 72 9 9, g32p_row26_traceSegment_061_0072_0009, g32p_row26_traceSegment_061_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 90 9 9, g32p_row26_traceSegment_061_0090_0009, g32p_row26_traceSegment_061_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 72 18 18, g32p_row26_traceSegment_061_0072_0018, g32p_row26_traceSegment_061_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 108 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 117 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 108 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 108 9 9, g32p_row26_traceSegment_061_0108_0009, g32p_row26_traceSegment_061_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 126 9 9, g32p_row26_traceSegment_061_0126_0009, g32p_row26_traceSegment_061_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 108 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 108 18 18, g32p_row26_traceSegment_061_0108_0018, g32p_row26_traceSegment_061_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 72 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 72 36 36, g32p_row26_traceSegment_061_0072_0036, g32p_row26_traceSegment_061_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_061 0 144 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 0 72 72, g32p_row26_traceSegment_061_0000_0072, g32p_row26_traceSegment_061_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 144 9 9, g32p_row26_traceSegment_061_0144_0009, g32p_row26_traceSegment_061_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 162 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 162 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 162 9 9, g32p_row26_traceSegment_061_0162_0009, g32p_row26_traceSegment_061_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 144 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 144 18 18, g32p_row26_traceSegment_061_0144_0018, g32p_row26_traceSegment_061_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 180 9 9, g32p_row26_traceSegment_061_0180_0009, g32p_row26_traceSegment_061_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 198 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 198 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 198 9 9, g32p_row26_traceSegment_061_0198_0009, g32p_row26_traceSegment_061_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 180 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 180 18 18, g32p_row26_traceSegment_061_0180_0018, g32p_row26_traceSegment_061_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 144 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 144 36 36, g32p_row26_traceSegment_061_0144_0036, g32p_row26_traceSegment_061_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 216 9 9, g32p_row26_traceSegment_061_0216_0009, g32p_row26_traceSegment_061_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 234 9 9, g32p_row26_traceSegment_061_0234_0009, g32p_row26_traceSegment_061_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 216 18 18, g32p_row26_traceSegment_061_0216_0018, g32p_row26_traceSegment_061_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 252 9 9, g32p_row26_traceSegment_061_0252_0009, g32p_row26_traceSegment_061_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 270 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 279 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 270 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 270 9 9, g32p_row26_traceSegment_061_0270_0009, g32p_row26_traceSegment_061_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 252 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 252 18 18, g32p_row26_traceSegment_061_0252_0018, g32p_row26_traceSegment_061_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 216 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 216 36 36, g32p_row26_traceSegment_061_0216_0036, g32p_row26_traceSegment_061_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_061 144 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 144 72 72, g32p_row26_traceSegment_061_0144_0072, g32p_row26_traceSegment_061_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_061 0 288 = [2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 0 144 144, g32p_row26_traceSegment_061_0000_0144, g32p_row26_traceSegment_061_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 288 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 288 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 288 9 9, g32p_row26_traceSegment_061_0288_0009, g32p_row26_traceSegment_061_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 306 9 9, g32p_row26_traceSegment_061_0306_0009, g32p_row26_traceSegment_061_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 288 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 288 18 18, g32p_row26_traceSegment_061_0288_0018, g32p_row26_traceSegment_061_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 324 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 324 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 324 9 9, g32p_row26_traceSegment_061_0324_0009, g32p_row26_traceSegment_061_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 342 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 342 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 342 9 9, g32p_row26_traceSegment_061_0342_0009, g32p_row26_traceSegment_061_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 324 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 324 18 18, g32p_row26_traceSegment_061_0324_0018, g32p_row26_traceSegment_061_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 288 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 288 36 36, g32p_row26_traceSegment_061_0288_0036, g32p_row26_traceSegment_061_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 360 9 9, g32p_row26_traceSegment_061_0360_0009, g32p_row26_traceSegment_061_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 378 9 9, g32p_row26_traceSegment_061_0378_0009, g32p_row26_traceSegment_061_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 360 18 18, g32p_row26_traceSegment_061_0360_0018, g32p_row26_traceSegment_061_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 396 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 396 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 396 9 9, g32p_row26_traceSegment_061_0396_0009, g32p_row26_traceSegment_061_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 414 9 9, g32p_row26_traceSegment_061_0414_0009, g32p_row26_traceSegment_061_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 396 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 396 18 18, g32p_row26_traceSegment_061_0396_0018, g32p_row26_traceSegment_061_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 360 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 360 36 36, g32p_row26_traceSegment_061_0360_0036, g32p_row26_traceSegment_061_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_061 288 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 288 72 72, g32p_row26_traceSegment_061_0288_0072, g32p_row26_traceSegment_061_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 441 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 432 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 432 9 9, g32p_row26_traceSegment_061_0432_0009, g32p_row26_traceSegment_061_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 459 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 450 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 450 9 9, g32p_row26_traceSegment_061_0450_0009, g32p_row26_traceSegment_061_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 432 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 432 18 18, g32p_row26_traceSegment_061_0432_0018, g32p_row26_traceSegment_061_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 468 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 468 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 468 9 9, g32p_row26_traceSegment_061_0468_0009, g32p_row26_traceSegment_061_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 486 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 486 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 486 9 9, g32p_row26_traceSegment_061_0486_0009, g32p_row26_traceSegment_061_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 468 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 468 18 18, g32p_row26_traceSegment_061_0468_0018, g32p_row26_traceSegment_061_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 432 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 432 36 36, g32p_row26_traceSegment_061_0432_0036, g32p_row26_traceSegment_061_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 504 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 504 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 504 9 9, g32p_row26_traceSegment_061_0504_0009, g32p_row26_traceSegment_061_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 531 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 522 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 522 9 9, g32p_row26_traceSegment_061_0522_0009, g32p_row26_traceSegment_061_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 504 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 504 18 18, g32p_row26_traceSegment_061_0504_0018, g32p_row26_traceSegment_061_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 540 9 = [3, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 549 9 = [3] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 540 18 = [6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 540 9 9, g32p_row26_traceSegment_061_0540_0009, g32p_row26_traceSegment_061_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_061 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_061_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_061 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 558 9 9, g32p_row26_traceSegment_061_0558_0009, g32p_row26_traceSegment_061_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_061 540 36 = [6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 540 18 18, g32p_row26_traceSegment_061_0540_0018, g32p_row26_traceSegment_061_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_061 504 72 = [6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 504 36 36, g32p_row26_traceSegment_061_0504_0036, g32p_row26_traceSegment_061_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_061 432 144 = [6, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 432 72 72, g32p_row26_traceSegment_061_0432_0072, g32p_row26_traceSegment_061_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_061 288 288 = [6, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 288 144 144, g32p_row26_traceSegment_061_0288_0144, g32p_row26_traceSegment_061_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_061_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_061 0 576 = [8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_061 0 288 288, g32p_row26_traceSegment_061_0000_0288, g32p_row26_traceSegment_061_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 61 = [8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_061_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_063 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 63 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_063_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 9 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 0 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 0 9 9, g32p_row26_traceSegment_063_0000_0009, g32p_row26_traceSegment_063_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 18 9 9, g32p_row26_traceSegment_063_0018_0009, g32p_row26_traceSegment_063_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 0 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 0 18 18, g32p_row26_traceSegment_063_0000_0018, g32p_row26_traceSegment_063_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 36 9 9, g32p_row26_traceSegment_063_0036_0009, g32p_row26_traceSegment_063_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 54 9 9, g32p_row26_traceSegment_063_0054_0009, g32p_row26_traceSegment_063_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 36 18 18, g32p_row26_traceSegment_063_0036_0018, g32p_row26_traceSegment_063_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 0 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 0 36 36, g32p_row26_traceSegment_063_0000_0036, g32p_row26_traceSegment_063_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 81 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 72 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 72 9 9, g32p_row26_traceSegment_063_0072_0009, g32p_row26_traceSegment_063_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 99 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 90 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 90 9 9, g32p_row26_traceSegment_063_0090_0009, g32p_row26_traceSegment_063_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 72 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 72 18 18, g32p_row26_traceSegment_063_0072_0018, g32p_row26_traceSegment_063_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 117 9 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 108 18 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 108 9 9, g32p_row26_traceSegment_063_0108_0009, g32p_row26_traceSegment_063_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 126 9 9, g32p_row26_traceSegment_063_0126_0009, g32p_row26_traceSegment_063_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 108 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 108 18 18, g32p_row26_traceSegment_063_0108_0018, g32p_row26_traceSegment_063_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 72 72 = [0, 0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 72 36 36, g32p_row26_traceSegment_063_0072_0036, g32p_row26_traceSegment_063_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_063 0 144 = [0, 0, 4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 0 72 72, g32p_row26_traceSegment_063_0000_0072, g32p_row26_traceSegment_063_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 144 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 153 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 144 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 144 9 9, g32p_row26_traceSegment_063_0144_0009, g32p_row26_traceSegment_063_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 162 9 9, g32p_row26_traceSegment_063_0162_0009, g32p_row26_traceSegment_063_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 144 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 144 18 18, g32p_row26_traceSegment_063_0144_0018, g32p_row26_traceSegment_063_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 180 9 9, g32p_row26_traceSegment_063_0180_0009, g32p_row26_traceSegment_063_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 198 9 9, g32p_row26_traceSegment_063_0198_0009, g32p_row26_traceSegment_063_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 180 18 18, g32p_row26_traceSegment_063_0180_0018, g32p_row26_traceSegment_063_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 144 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 144 36 36, g32p_row26_traceSegment_063_0144_0036, g32p_row26_traceSegment_063_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 216 9 9, g32p_row26_traceSegment_063_0216_0009, g32p_row26_traceSegment_063_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 234 9 9, g32p_row26_traceSegment_063_0234_0009, g32p_row26_traceSegment_063_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 216 18 18, g32p_row26_traceSegment_063_0216_0018, g32p_row26_traceSegment_063_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 261 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 252 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 252 9 9, g32p_row26_traceSegment_063_0252_0009, g32p_row26_traceSegment_063_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 270 9 9, g32p_row26_traceSegment_063_0270_0009, g32p_row26_traceSegment_063_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 252 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 252 18 18, g32p_row26_traceSegment_063_0252_0018, g32p_row26_traceSegment_063_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 216 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 216 36 36, g32p_row26_traceSegment_063_0216_0036, g32p_row26_traceSegment_063_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_063 144 144 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 144 72 72, g32p_row26_traceSegment_063_0144_0072, g32p_row26_traceSegment_063_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_063 0 288 = [0, 0, 4, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 0 144 144, g32p_row26_traceSegment_063_0000_0144, g32p_row26_traceSegment_063_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 288 9 9, g32p_row26_traceSegment_063_0288_0009, g32p_row26_traceSegment_063_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 306 9 9, g32p_row26_traceSegment_063_0306_0009, g32p_row26_traceSegment_063_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 288 18 18, g32p_row26_traceSegment_063_0288_0018, g32p_row26_traceSegment_063_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 324 9 9, g32p_row26_traceSegment_063_0324_0009, g32p_row26_traceSegment_063_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 351 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 342 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 342 9 9, g32p_row26_traceSegment_063_0342_0009, g32p_row26_traceSegment_063_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 324 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 324 18 18, g32p_row26_traceSegment_063_0324_0018, g32p_row26_traceSegment_063_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 288 72 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 288 36 36, g32p_row26_traceSegment_063_0288_0036, g32p_row26_traceSegment_063_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 360 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 369 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 360 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 360 9 9, g32p_row26_traceSegment_063_0360_0009, g32p_row26_traceSegment_063_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 378 9 9, g32p_row26_traceSegment_063_0378_0009, g32p_row26_traceSegment_063_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 360 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 360 18 18, g32p_row26_traceSegment_063_0360_0018, g32p_row26_traceSegment_063_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 396 9 9, g32p_row26_traceSegment_063_0396_0009, g32p_row26_traceSegment_063_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 423 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 414 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 414 9 9, g32p_row26_traceSegment_063_0414_0009, g32p_row26_traceSegment_063_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 396 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 396 18 18, g32p_row26_traceSegment_063_0396_0018, g32p_row26_traceSegment_063_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 360 72 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 360 36 36, g32p_row26_traceSegment_063_0360_0036, g32p_row26_traceSegment_063_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_063 288 144 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 288 72 72, g32p_row26_traceSegment_063_0288_0072, g32p_row26_traceSegment_063_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 441 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 432 9 9, g32p_row26_traceSegment_063_0432_0009, g32p_row26_traceSegment_063_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 450 9 9, g32p_row26_traceSegment_063_0450_0009, g32p_row26_traceSegment_063_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 432 18 18, g32p_row26_traceSegment_063_0432_0018, g32p_row26_traceSegment_063_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 468 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 468 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 468 9 9, g32p_row26_traceSegment_063_0468_0009, g32p_row26_traceSegment_063_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 486 9 9, g32p_row26_traceSegment_063_0486_0009, g32p_row26_traceSegment_063_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 468 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 468 18 18, g32p_row26_traceSegment_063_0468_0018, g32p_row26_traceSegment_063_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 432 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 432 36 36, g32p_row26_traceSegment_063_0432_0036, g32p_row26_traceSegment_063_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 513 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 504 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 504 9 9, g32p_row26_traceSegment_063_0504_0009, g32p_row26_traceSegment_063_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 522 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 522 9 9, g32p_row26_traceSegment_063_0522_0009, g32p_row26_traceSegment_063_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 504 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 504 18 18, g32p_row26_traceSegment_063_0504_0018, g32p_row26_traceSegment_063_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 540 9 9, g32p_row26_traceSegment_063_0540_0009, g32p_row26_traceSegment_063_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_063 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_063_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_063 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 558 9 9, g32p_row26_traceSegment_063_0558_0009, g32p_row26_traceSegment_063_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_063 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 540 18 18, g32p_row26_traceSegment_063_0540_0018, g32p_row26_traceSegment_063_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_063 504 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 504 36 36, g32p_row26_traceSegment_063_0504_0036, g32p_row26_traceSegment_063_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_063 432 144 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 432 72 72, g32p_row26_traceSegment_063_0432_0072, g32p_row26_traceSegment_063_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_063 288 288 = [0, 0, 4, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 288 144 144, g32p_row26_traceSegment_063_0288_0144, g32p_row26_traceSegment_063_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_063_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_063 0 576 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_063 0 288 288, g32p_row26_traceSegment_063_0000_0288, g32p_row26_traceSegment_063_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 63 = [0, 0, 8, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_063_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_064 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 64 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_064_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 0 9 9, g32p_row26_traceSegment_064_0000_0009, g32p_row26_traceSegment_064_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 18 9 9, g32p_row26_traceSegment_064_0018_0009, g32p_row26_traceSegment_064_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 0 18 18, g32p_row26_traceSegment_064_0000_0018, g32p_row26_traceSegment_064_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 36 9 9, g32p_row26_traceSegment_064_0036_0009, g32p_row26_traceSegment_064_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 54 9 9, g32p_row26_traceSegment_064_0054_0009, g32p_row26_traceSegment_064_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 36 18 18, g32p_row26_traceSegment_064_0036_0018, g32p_row26_traceSegment_064_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 0 36 36, g32p_row26_traceSegment_064_0000_0036, g32p_row26_traceSegment_064_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 72 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 72 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 72 9 9, g32p_row26_traceSegment_064_0072_0009, g32p_row26_traceSegment_064_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 90 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 90 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 90 9 9, g32p_row26_traceSegment_064_0090_0009, g32p_row26_traceSegment_064_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 72 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 72 18 18, g32p_row26_traceSegment_064_0072_0018, g32p_row26_traceSegment_064_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 108 9 9, g32p_row26_traceSegment_064_0108_0009, g32p_row26_traceSegment_064_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 126 9 9, g32p_row26_traceSegment_064_0126_0009, g32p_row26_traceSegment_064_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 108 18 18, g32p_row26_traceSegment_064_0108_0018, g32p_row26_traceSegment_064_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 72 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 72 36 36, g32p_row26_traceSegment_064_0072_0036, g32p_row26_traceSegment_064_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_064 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 0 72 72, g32p_row26_traceSegment_064_0000_0072, g32p_row26_traceSegment_064_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 144 9 9, g32p_row26_traceSegment_064_0144_0009, g32p_row26_traceSegment_064_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 162 9 9, g32p_row26_traceSegment_064_0162_0009, g32p_row26_traceSegment_064_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 144 18 18, g32p_row26_traceSegment_064_0144_0018, g32p_row26_traceSegment_064_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 180 9 9, g32p_row26_traceSegment_064_0180_0009, g32p_row26_traceSegment_064_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 198 9 9, g32p_row26_traceSegment_064_0198_0009, g32p_row26_traceSegment_064_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 180 18 18, g32p_row26_traceSegment_064_0180_0018, g32p_row26_traceSegment_064_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 144 36 36, g32p_row26_traceSegment_064_0144_0036, g32p_row26_traceSegment_064_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 216 9 9, g32p_row26_traceSegment_064_0216_0009, g32p_row26_traceSegment_064_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 234 9 9, g32p_row26_traceSegment_064_0234_0009, g32p_row26_traceSegment_064_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 216 18 18, g32p_row26_traceSegment_064_0216_0018, g32p_row26_traceSegment_064_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 252 9 9, g32p_row26_traceSegment_064_0252_0009, g32p_row26_traceSegment_064_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 270 9 9, g32p_row26_traceSegment_064_0270_0009, g32p_row26_traceSegment_064_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 252 18 18, g32p_row26_traceSegment_064_0252_0018, g32p_row26_traceSegment_064_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 216 36 36, g32p_row26_traceSegment_064_0216_0036, g32p_row26_traceSegment_064_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_064 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 144 72 72, g32p_row26_traceSegment_064_0144_0072, g32p_row26_traceSegment_064_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_064 0 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 0 144 144, g32p_row26_traceSegment_064_0000_0144, g32p_row26_traceSegment_064_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 288 9 9, g32p_row26_traceSegment_064_0288_0009, g32p_row26_traceSegment_064_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 315 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 306 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 306 9 9, g32p_row26_traceSegment_064_0306_0009, g32p_row26_traceSegment_064_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 288 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 288 18 18, g32p_row26_traceSegment_064_0288_0018, g32p_row26_traceSegment_064_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 324 9 9, g32p_row26_traceSegment_064_0324_0009, g32p_row26_traceSegment_064_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 342 9 9, g32p_row26_traceSegment_064_0342_0009, g32p_row26_traceSegment_064_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 324 18 18, g32p_row26_traceSegment_064_0324_0018, g32p_row26_traceSegment_064_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 288 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 288 36 36, g32p_row26_traceSegment_064_0288_0036, g32p_row26_traceSegment_064_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 369 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 360 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 360 9 9, g32p_row26_traceSegment_064_0360_0009, g32p_row26_traceSegment_064_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 378 9 9, g32p_row26_traceSegment_064_0378_0009, g32p_row26_traceSegment_064_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 360 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 360 18 18, g32p_row26_traceSegment_064_0360_0018, g32p_row26_traceSegment_064_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 396 9 9, g32p_row26_traceSegment_064_0396_0009, g32p_row26_traceSegment_064_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 414 9 9, g32p_row26_traceSegment_064_0414_0009, g32p_row26_traceSegment_064_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 396 18 18, g32p_row26_traceSegment_064_0396_0018, g32p_row26_traceSegment_064_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 360 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 360 36 36, g32p_row26_traceSegment_064_0360_0036, g32p_row26_traceSegment_064_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_064 288 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 288 72 72, g32p_row26_traceSegment_064_0288_0072, g32p_row26_traceSegment_064_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 432 9 9, g32p_row26_traceSegment_064_0432_0009, g32p_row26_traceSegment_064_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 450 9 9, g32p_row26_traceSegment_064_0450_0009, g32p_row26_traceSegment_064_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 432 18 18, g32p_row26_traceSegment_064_0432_0018, g32p_row26_traceSegment_064_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 468 9 9, g32p_row26_traceSegment_064_0468_0009, g32p_row26_traceSegment_064_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 486 9 9, g32p_row26_traceSegment_064_0486_0009, g32p_row26_traceSegment_064_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 468 18 18, g32p_row26_traceSegment_064_0468_0018, g32p_row26_traceSegment_064_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 432 36 36, g32p_row26_traceSegment_064_0432_0036, g32p_row26_traceSegment_064_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 504 9 9, g32p_row26_traceSegment_064_0504_0009, g32p_row26_traceSegment_064_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 522 9 9, g32p_row26_traceSegment_064_0522_0009, g32p_row26_traceSegment_064_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 504 18 18, g32p_row26_traceSegment_064_0504_0018, g32p_row26_traceSegment_064_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 540 9 9, g32p_row26_traceSegment_064_0540_0009, g32p_row26_traceSegment_064_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_064 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_064_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_064 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 558 9 9, g32p_row26_traceSegment_064_0558_0009, g32p_row26_traceSegment_064_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_064 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 540 18 18, g32p_row26_traceSegment_064_0540_0018, g32p_row26_traceSegment_064_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_064 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 504 36 36, g32p_row26_traceSegment_064_0504_0036, g32p_row26_traceSegment_064_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_064 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 432 72 72, g32p_row26_traceSegment_064_0432_0072, g32p_row26_traceSegment_064_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_064 288 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 288 144 144, g32p_row26_traceSegment_064_0288_0144, g32p_row26_traceSegment_064_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_064_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_064 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_064 0 288 288, g32p_row26_traceSegment_064_0000_0288, g32p_row26_traceSegment_064_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 64 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_064_0000_0576

end HodgeLean.Foundations.Program

end
end
