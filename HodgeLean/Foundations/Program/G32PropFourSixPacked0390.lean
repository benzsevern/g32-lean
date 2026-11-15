import HodgeLean.Foundations.Program.G32PropFourSixPacked0388
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0389

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_057_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 0 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 9 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 0 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 0 9 9, g32p_row22_traceSegment_057_0000_0009, g32p_row22_traceSegment_057_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 18 9 9, g32p_row22_traceSegment_057_0018_0009, g32p_row22_traceSegment_057_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 0 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 0 18 18, g32p_row22_traceSegment_057_0000_0018, g32p_row22_traceSegment_057_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 36 9 9, g32p_row22_traceSegment_057_0036_0009, g32p_row22_traceSegment_057_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 54 9 9, g32p_row22_traceSegment_057_0054_0009, g32p_row22_traceSegment_057_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 36 18 18, g32p_row22_traceSegment_057_0036_0018, g32p_row22_traceSegment_057_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 0 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 0 36 36, g32p_row22_traceSegment_057_0000_0036, g32p_row22_traceSegment_057_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 72 9 9, g32p_row22_traceSegment_057_0072_0009, g32p_row22_traceSegment_057_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 90 9 9, g32p_row22_traceSegment_057_0090_0009, g32p_row22_traceSegment_057_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 72 18 18, g32p_row22_traceSegment_057_0072_0018, g32p_row22_traceSegment_057_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 108 9 9, g32p_row22_traceSegment_057_0108_0009, g32p_row22_traceSegment_057_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 126 9 9, g32p_row22_traceSegment_057_0126_0009, g32p_row22_traceSegment_057_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 108 18 18, g32p_row22_traceSegment_057_0108_0018, g32p_row22_traceSegment_057_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 72 36 36, g32p_row22_traceSegment_057_0072_0036, g32p_row22_traceSegment_057_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_057 0 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 0 72 72, g32p_row22_traceSegment_057_0000_0072, g32p_row22_traceSegment_057_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 144 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 153 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 144 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 144 9 9, g32p_row22_traceSegment_057_0144_0009, g32p_row22_traceSegment_057_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 162 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 162 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 162 9 9, g32p_row22_traceSegment_057_0162_0009, g32p_row22_traceSegment_057_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 144 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 144 18 18, g32p_row22_traceSegment_057_0144_0018, g32p_row22_traceSegment_057_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 180 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 189 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 180 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 180 9 9, g32p_row22_traceSegment_057_0180_0009, g32p_row22_traceSegment_057_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 207 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 198 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 198 9 9, g32p_row22_traceSegment_057_0198_0009, g32p_row22_traceSegment_057_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 180 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 180 18 18, g32p_row22_traceSegment_057_0180_0018, g32p_row22_traceSegment_057_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 144 72 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 144 36 36, g32p_row22_traceSegment_057_0144_0036, g32p_row22_traceSegment_057_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 216 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 225 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 216 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 216 9 9, g32p_row22_traceSegment_057_0216_0009, g32p_row22_traceSegment_057_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 234 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 243 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 234 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 234 9 9, g32p_row22_traceSegment_057_0234_0009, g32p_row22_traceSegment_057_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 216 36 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 216 18 18, g32p_row22_traceSegment_057_0216_0018, g32p_row22_traceSegment_057_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 252 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 252 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 252 9 9, g32p_row22_traceSegment_057_0252_0009, g32p_row22_traceSegment_057_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 270 9 9, g32p_row22_traceSegment_057_0270_0009, g32p_row22_traceSegment_057_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 252 18 18, g32p_row22_traceSegment_057_0252_0018, g32p_row22_traceSegment_057_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 216 72 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 216 36 36, g32p_row22_traceSegment_057_0216_0036, g32p_row22_traceSegment_057_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_057 144 144 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 144 72 72, g32p_row22_traceSegment_057_0144_0072, g32p_row22_traceSegment_057_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_057 0 288 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 0 144 144, g32p_row22_traceSegment_057_0000_0144, g32p_row22_traceSegment_057_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 288 9 9, g32p_row22_traceSegment_057_0288_0009, g32p_row22_traceSegment_057_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 306 9 9, g32p_row22_traceSegment_057_0306_0009, g32p_row22_traceSegment_057_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 288 18 18, g32p_row22_traceSegment_057_0288_0018, g32p_row22_traceSegment_057_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 324 9 9, g32p_row22_traceSegment_057_0324_0009, g32p_row22_traceSegment_057_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 351 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 342 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 342 9 9, g32p_row22_traceSegment_057_0342_0009, g32p_row22_traceSegment_057_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 324 18 18, g32p_row22_traceSegment_057_0324_0018, g32p_row22_traceSegment_057_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 288 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 288 36 36, g32p_row22_traceSegment_057_0288_0036, g32p_row22_traceSegment_057_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 360 9 9, g32p_row22_traceSegment_057_0360_0009, g32p_row22_traceSegment_057_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 378 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 387 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 378 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 378 9 9, g32p_row22_traceSegment_057_0378_0009, g32p_row22_traceSegment_057_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 360 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 360 18 18, g32p_row22_traceSegment_057_0360_0018, g32p_row22_traceSegment_057_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 405 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 396 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 396 9 9, g32p_row22_traceSegment_057_0396_0009, g32p_row22_traceSegment_057_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 414 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 423 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 414 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 414 9 9, g32p_row22_traceSegment_057_0414_0009, g32p_row22_traceSegment_057_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 396 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 396 18 18, g32p_row22_traceSegment_057_0396_0018, g32p_row22_traceSegment_057_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 360 72 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 360 36 36, g32p_row22_traceSegment_057_0360_0036, g32p_row22_traceSegment_057_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_057 288 144 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 288 72 72, g32p_row22_traceSegment_057_0288_0072, g32p_row22_traceSegment_057_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 432 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 441 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 432 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 432 9 9, g32p_row22_traceSegment_057_0432_0009, g32p_row22_traceSegment_057_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 450 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 459 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 450 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 450 9 9, g32p_row22_traceSegment_057_0450_0009, g32p_row22_traceSegment_057_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 432 36 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 432 18 18, g32p_row22_traceSegment_057_0432_0018, g32p_row22_traceSegment_057_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 468 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 477 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 468 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 468 9 9, g32p_row22_traceSegment_057_0468_0009, g32p_row22_traceSegment_057_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 486 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 486 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 486 9 9, g32p_row22_traceSegment_057_0486_0009, g32p_row22_traceSegment_057_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 468 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 468 18 18, g32p_row22_traceSegment_057_0468_0018, g32p_row22_traceSegment_057_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 432 72 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 432 36 36, g32p_row22_traceSegment_057_0432_0036, g32p_row22_traceSegment_057_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 504 9 9, g32p_row22_traceSegment_057_0504_0009, g32p_row22_traceSegment_057_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 522 9 9, g32p_row22_traceSegment_057_0522_0009, g32p_row22_traceSegment_057_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 504 18 18, g32p_row22_traceSegment_057_0504_0018, g32p_row22_traceSegment_057_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 549 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 540 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 540 9 9, g32p_row22_traceSegment_057_0540_0009, g32p_row22_traceSegment_057_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 558 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_057 567 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_057_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_057 558 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 558 9 9, g32p_row22_traceSegment_057_0558_0009, g32p_row22_traceSegment_057_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_057 540 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 540 18 18, g32p_row22_traceSegment_057_0540_0018, g32p_row22_traceSegment_057_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_057 504 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 504 36 36, g32p_row22_traceSegment_057_0504_0036, g32p_row22_traceSegment_057_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_057 432 144 = [0, 21] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 432 72 72, g32p_row22_traceSegment_057_0432_0072, g32p_row22_traceSegment_057_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_057 288 288 = [0, 30] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 288 144 144, g32p_row22_traceSegment_057_0288_0144, g32p_row22_traceSegment_057_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_057_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_057 0 576 = [0, 48] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_057 0 288 288, g32p_row22_traceSegment_057_0000_0288, g32p_row22_traceSegment_057_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 57 = [0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_057_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_059 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 59 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_059_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 0 9 9, g32p_row22_traceSegment_059_0000_0009, g32p_row22_traceSegment_059_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 18 9 9, g32p_row22_traceSegment_059_0018_0009, g32p_row22_traceSegment_059_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 0 18 18, g32p_row22_traceSegment_059_0000_0018, g32p_row22_traceSegment_059_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 45 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 36 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 36 9 9, g32p_row22_traceSegment_059_0036_0009, g32p_row22_traceSegment_059_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 54 9 9, g32p_row22_traceSegment_059_0054_0009, g32p_row22_traceSegment_059_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 36 18 18, g32p_row22_traceSegment_059_0036_0018, g32p_row22_traceSegment_059_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 0 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 0 36 36, g32p_row22_traceSegment_059_0000_0036, g32p_row22_traceSegment_059_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 72 9 9, g32p_row22_traceSegment_059_0072_0009, g32p_row22_traceSegment_059_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 90 9 9, g32p_row22_traceSegment_059_0090_0009, g32p_row22_traceSegment_059_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 72 18 18, g32p_row22_traceSegment_059_0072_0018, g32p_row22_traceSegment_059_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 108 9 9, g32p_row22_traceSegment_059_0108_0009, g32p_row22_traceSegment_059_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 126 9 9, g32p_row22_traceSegment_059_0126_0009, g32p_row22_traceSegment_059_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 108 18 18, g32p_row22_traceSegment_059_0108_0018, g32p_row22_traceSegment_059_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 72 36 36, g32p_row22_traceSegment_059_0072_0036, g32p_row22_traceSegment_059_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_059 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 0 72 72, g32p_row22_traceSegment_059_0000_0072, g32p_row22_traceSegment_059_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 153 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 144 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 144 9 9, g32p_row22_traceSegment_059_0144_0009, g32p_row22_traceSegment_059_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 162 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 171 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 162 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 162 9 9, g32p_row22_traceSegment_059_0162_0009, g32p_row22_traceSegment_059_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 144 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 144 18 18, g32p_row22_traceSegment_059_0144_0018, g32p_row22_traceSegment_059_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 180 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 180 9 9, g32p_row22_traceSegment_059_0180_0009, g32p_row22_traceSegment_059_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 198 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 198 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 198 9 9, g32p_row22_traceSegment_059_0198_0009, g32p_row22_traceSegment_059_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 180 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 180 18 18, g32p_row22_traceSegment_059_0180_0018, g32p_row22_traceSegment_059_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 144 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 144 36 36, g32p_row22_traceSegment_059_0144_0036, g32p_row22_traceSegment_059_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 225 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 216 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 216 9 9, g32p_row22_traceSegment_059_0216_0009, g32p_row22_traceSegment_059_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 234 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 234 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 234 9 9, g32p_row22_traceSegment_059_0234_0009, g32p_row22_traceSegment_059_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 216 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 216 18 18, g32p_row22_traceSegment_059_0216_0018, g32p_row22_traceSegment_059_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 252 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 252 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 252 9 9, g32p_row22_traceSegment_059_0252_0009, g32p_row22_traceSegment_059_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 270 9 9, g32p_row22_traceSegment_059_0270_0009, g32p_row22_traceSegment_059_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 252 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 252 18 18, g32p_row22_traceSegment_059_0252_0018, g32p_row22_traceSegment_059_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 216 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 216 36 36, g32p_row22_traceSegment_059_0216_0036, g32p_row22_traceSegment_059_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_059 144 144 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 144 72 72, g32p_row22_traceSegment_059_0144_0072, g32p_row22_traceSegment_059_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_059 0 288 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 0 144 144, g32p_row22_traceSegment_059_0000_0144, g32p_row22_traceSegment_059_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 288 9 9, g32p_row22_traceSegment_059_0288_0009, g32p_row22_traceSegment_059_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 306 9 9, g32p_row22_traceSegment_059_0306_0009, g32p_row22_traceSegment_059_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 288 18 18, g32p_row22_traceSegment_059_0288_0018, g32p_row22_traceSegment_059_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 324 9 9, g32p_row22_traceSegment_059_0324_0009, g32p_row22_traceSegment_059_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 342 9 9, g32p_row22_traceSegment_059_0342_0009, g32p_row22_traceSegment_059_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 324 18 18, g32p_row22_traceSegment_059_0324_0018, g32p_row22_traceSegment_059_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 288 36 36, g32p_row22_traceSegment_059_0288_0036, g32p_row22_traceSegment_059_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 360 9 9, g32p_row22_traceSegment_059_0360_0009, g32p_row22_traceSegment_059_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 387 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 378 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 378 9 9, g32p_row22_traceSegment_059_0378_0009, g32p_row22_traceSegment_059_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 360 18 18, g32p_row22_traceSegment_059_0360_0018, g32p_row22_traceSegment_059_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 396 9 9, g32p_row22_traceSegment_059_0396_0009, g32p_row22_traceSegment_059_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 414 9 9, g32p_row22_traceSegment_059_0414_0009, g32p_row22_traceSegment_059_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 396 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 396 18 18, g32p_row22_traceSegment_059_0396_0018, g32p_row22_traceSegment_059_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 360 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 360 36 36, g32p_row22_traceSegment_059_0360_0036, g32p_row22_traceSegment_059_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_059 288 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 288 72 72, g32p_row22_traceSegment_059_0288_0072, g32p_row22_traceSegment_059_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 432 9 9, g32p_row22_traceSegment_059_0432_0009, g32p_row22_traceSegment_059_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 450 9 9, g32p_row22_traceSegment_059_0450_0009, g32p_row22_traceSegment_059_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 432 18 18, g32p_row22_traceSegment_059_0432_0018, g32p_row22_traceSegment_059_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 468 9 9, g32p_row22_traceSegment_059_0468_0009, g32p_row22_traceSegment_059_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 486 9 9, g32p_row22_traceSegment_059_0486_0009, g32p_row22_traceSegment_059_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 468 18 18, g32p_row22_traceSegment_059_0468_0018, g32p_row22_traceSegment_059_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 432 36 36, g32p_row22_traceSegment_059_0432_0036, g32p_row22_traceSegment_059_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 504 9 9, g32p_row22_traceSegment_059_0504_0009, g32p_row22_traceSegment_059_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 522 9 9, g32p_row22_traceSegment_059_0522_0009, g32p_row22_traceSegment_059_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 504 18 18, g32p_row22_traceSegment_059_0504_0018, g32p_row22_traceSegment_059_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 540 9 9, g32p_row22_traceSegment_059_0540_0009, g32p_row22_traceSegment_059_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 558 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_059 567 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_059_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_059 558 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 558 9 9, g32p_row22_traceSegment_059_0558_0009, g32p_row22_traceSegment_059_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_059 540 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 540 18 18, g32p_row22_traceSegment_059_0540_0018, g32p_row22_traceSegment_059_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_059 504 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 504 36 36, g32p_row22_traceSegment_059_0504_0036, g32p_row22_traceSegment_059_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_059 432 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 432 72 72, g32p_row22_traceSegment_059_0432_0072, g32p_row22_traceSegment_059_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_059 288 288 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 288 144 144, g32p_row22_traceSegment_059_0288_0144, g32p_row22_traceSegment_059_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_059_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_059 0 576 = [0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_059 0 288 288, g32p_row22_traceSegment_059_0000_0288, g32p_row22_traceSegment_059_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 59 = [0, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_059_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_065_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 0 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 0 9 9, g32p_row22_traceSegment_065_0000_0009, g32p_row22_traceSegment_065_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 18 9 9, g32p_row22_traceSegment_065_0018_0009, g32p_row22_traceSegment_065_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 0 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 0 18 18, g32p_row22_traceSegment_065_0000_0018, g32p_row22_traceSegment_065_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 36 9 9, g32p_row22_traceSegment_065_0036_0009, g32p_row22_traceSegment_065_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 63 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 54 9 9, g32p_row22_traceSegment_065_0054_0009, g32p_row22_traceSegment_065_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 36 18 18, g32p_row22_traceSegment_065_0036_0018, g32p_row22_traceSegment_065_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 0 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 0 36 36, g32p_row22_traceSegment_065_0000_0036, g32p_row22_traceSegment_065_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 72 9 9, g32p_row22_traceSegment_065_0072_0009, g32p_row22_traceSegment_065_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 90 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 90 9 9, g32p_row22_traceSegment_065_0090_0009, g32p_row22_traceSegment_065_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 72 18 18, g32p_row22_traceSegment_065_0072_0018, g32p_row22_traceSegment_065_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 108 9 9, g32p_row22_traceSegment_065_0108_0009, g32p_row22_traceSegment_065_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 126 9 9, g32p_row22_traceSegment_065_0126_0009, g32p_row22_traceSegment_065_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 108 18 18, g32p_row22_traceSegment_065_0108_0018, g32p_row22_traceSegment_065_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 72 36 36, g32p_row22_traceSegment_065_0072_0036, g32p_row22_traceSegment_065_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_065 0 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 0 72 72, g32p_row22_traceSegment_065_0000_0072, g32p_row22_traceSegment_065_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 144 9 9, g32p_row22_traceSegment_065_0144_0009, g32p_row22_traceSegment_065_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 162 9 9, g32p_row22_traceSegment_065_0162_0009, g32p_row22_traceSegment_065_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 144 18 18, g32p_row22_traceSegment_065_0144_0018, g32p_row22_traceSegment_065_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 180 9 9, g32p_row22_traceSegment_065_0180_0009, g32p_row22_traceSegment_065_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 198 9 9, g32p_row22_traceSegment_065_0198_0009, g32p_row22_traceSegment_065_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 180 18 18, g32p_row22_traceSegment_065_0180_0018, g32p_row22_traceSegment_065_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 144 36 36, g32p_row22_traceSegment_065_0144_0036, g32p_row22_traceSegment_065_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 216 9 9, g32p_row22_traceSegment_065_0216_0009, g32p_row22_traceSegment_065_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 234 9 9, g32p_row22_traceSegment_065_0234_0009, g32p_row22_traceSegment_065_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 216 18 18, g32p_row22_traceSegment_065_0216_0018, g32p_row22_traceSegment_065_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 252 9 9, g32p_row22_traceSegment_065_0252_0009, g32p_row22_traceSegment_065_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 270 9 9, g32p_row22_traceSegment_065_0270_0009, g32p_row22_traceSegment_065_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 252 18 18, g32p_row22_traceSegment_065_0252_0018, g32p_row22_traceSegment_065_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 216 36 36, g32p_row22_traceSegment_065_0216_0036, g32p_row22_traceSegment_065_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_065 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 144 72 72, g32p_row22_traceSegment_065_0144_0072, g32p_row22_traceSegment_065_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_065 0 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 0 144 144, g32p_row22_traceSegment_065_0000_0144, g32p_row22_traceSegment_065_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 288 9 9, g32p_row22_traceSegment_065_0288_0009, g32p_row22_traceSegment_065_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 306 9 9, g32p_row22_traceSegment_065_0306_0009, g32p_row22_traceSegment_065_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 288 18 18, g32p_row22_traceSegment_065_0288_0018, g32p_row22_traceSegment_065_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 324 9 9, g32p_row22_traceSegment_065_0324_0009, g32p_row22_traceSegment_065_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 342 9 9, g32p_row22_traceSegment_065_0342_0009, g32p_row22_traceSegment_065_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 324 18 18, g32p_row22_traceSegment_065_0324_0018, g32p_row22_traceSegment_065_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 288 36 36, g32p_row22_traceSegment_065_0288_0036, g32p_row22_traceSegment_065_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 360 9 9, g32p_row22_traceSegment_065_0360_0009, g32p_row22_traceSegment_065_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 378 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 378 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 378 9 9, g32p_row22_traceSegment_065_0378_0009, g32p_row22_traceSegment_065_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 360 18 18, g32p_row22_traceSegment_065_0360_0018, g32p_row22_traceSegment_065_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 396 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 396 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 396 9 9, g32p_row22_traceSegment_065_0396_0009, g32p_row22_traceSegment_065_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 414 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 414 9 9, g32p_row22_traceSegment_065_0414_0009, g32p_row22_traceSegment_065_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 396 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 396 18 18, g32p_row22_traceSegment_065_0396_0018, g32p_row22_traceSegment_065_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 360 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 360 36 36, g32p_row22_traceSegment_065_0360_0036, g32p_row22_traceSegment_065_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_065 288 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 288 72 72, g32p_row22_traceSegment_065_0288_0072, g32p_row22_traceSegment_065_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 432 9 9, g32p_row22_traceSegment_065_0432_0009, g32p_row22_traceSegment_065_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 459 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 450 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 450 9 9, g32p_row22_traceSegment_065_0450_0009, g32p_row22_traceSegment_065_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 432 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 432 18 18, g32p_row22_traceSegment_065_0432_0018, g32p_row22_traceSegment_065_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 477 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 468 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 468 9 9, g32p_row22_traceSegment_065_0468_0009, g32p_row22_traceSegment_065_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 486 9 9, g32p_row22_traceSegment_065_0486_0009, g32p_row22_traceSegment_065_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 468 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 468 18 18, g32p_row22_traceSegment_065_0468_0018, g32p_row22_traceSegment_065_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 432 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 432 36 36, g32p_row22_traceSegment_065_0432_0036, g32p_row22_traceSegment_065_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 504 9 9, g32p_row22_traceSegment_065_0504_0009, g32p_row22_traceSegment_065_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 522 9 9, g32p_row22_traceSegment_065_0522_0009, g32p_row22_traceSegment_065_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 504 18 18, g32p_row22_traceSegment_065_0504_0018, g32p_row22_traceSegment_065_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 540 9 9, g32p_row22_traceSegment_065_0540_0009, g32p_row22_traceSegment_065_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_065 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_065_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_065 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 558 9 9, g32p_row22_traceSegment_065_0558_0009, g32p_row22_traceSegment_065_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_065 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 540 18 18, g32p_row22_traceSegment_065_0540_0018, g32p_row22_traceSegment_065_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_065 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 504 36 36, g32p_row22_traceSegment_065_0504_0036, g32p_row22_traceSegment_065_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_065 432 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 432 72 72, g32p_row22_traceSegment_065_0432_0072, g32p_row22_traceSegment_065_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_065 288 288 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 288 144 144, g32p_row22_traceSegment_065_0288_0144, g32p_row22_traceSegment_065_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_065_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_065 0 576 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_065 0 288 288, g32p_row22_traceSegment_065_0000_0288, g32p_row22_traceSegment_065_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 65 = [0, 0, 0, 0, 10] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_065_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row22_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 46) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 46) (g32p_literalTraceValue 21 46)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_046]
  decide +kernel

theorem g32p_row22_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 49) (g32p_literalTraceValue 21 49)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row22_traceCoefficients_049]
  decide +kernel

theorem g32p_row22_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 50) (g32p_literalTraceValue 21 50)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_050]
  decide +kernel

theorem g32p_row22_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 52) (g32p_literalTraceValue 21 52)
      [1, -1, 1] [0, 0, 3456, 3456] = true := by
  rw [g32p_row22_traceCoefficients_052]
  decide +kernel

theorem g32p_row22_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 56) (g32p_literalTraceValue 21 56)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_056]
  decide +kernel

theorem g32p_row22_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 57) (g32p_literalTraceValue 21 57)
      [1, -1, 1] [-1152] = true := by
  rw [g32p_row22_traceCoefficients_057]
  decide +kernel

theorem g32p_row22_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 59) (g32p_literalTraceValue 21 59)
      [1, -1, 1] [1728, 1728, 1728] = true := by
  rw [g32p_row22_traceCoefficients_059]
  decide +kernel

theorem g32p_row22_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 65) (g32p_literalTraceValue 21 65)
      [1, -1, 1] [17280, 17280, 17280] = true := by
  rw [g32p_row22_traceCoefficients_065]
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

private def g32p_row22_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_069_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 0 9 9, g32p_row22_traceSegment_069_0000_0009, g32p_row22_traceSegment_069_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 27 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 18 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 18 9 9, g32p_row22_traceSegment_069_0018_0009, g32p_row22_traceSegment_069_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 0 18 18, g32p_row22_traceSegment_069_0000_0018, g32p_row22_traceSegment_069_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 36 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 36 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 36 9 9, g32p_row22_traceSegment_069_0036_0009, g32p_row22_traceSegment_069_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 54 9 9, g32p_row22_traceSegment_069_0054_0009, g32p_row22_traceSegment_069_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 36 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 36 18 18, g32p_row22_traceSegment_069_0036_0018, g32p_row22_traceSegment_069_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 0 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 0 36 36, g32p_row22_traceSegment_069_0000_0036, g32p_row22_traceSegment_069_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 72 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 72 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 72 9 9, g32p_row22_traceSegment_069_0072_0009, g32p_row22_traceSegment_069_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 90 9 9, g32p_row22_traceSegment_069_0090_0009, g32p_row22_traceSegment_069_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 72 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 72 18 18, g32p_row22_traceSegment_069_0072_0018, g32p_row22_traceSegment_069_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 108 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 117 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 108 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 108 9 9, g32p_row22_traceSegment_069_0108_0009, g32p_row22_traceSegment_069_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 126 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 126 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 126 9 9, g32p_row22_traceSegment_069_0126_0009, g32p_row22_traceSegment_069_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 108 36 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 108 18 18, g32p_row22_traceSegment_069_0108_0018, g32p_row22_traceSegment_069_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 72 72 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 72 36 36, g32p_row22_traceSegment_069_0072_0036, g32p_row22_traceSegment_069_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_069 0 144 = [2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 0 72 72, g32p_row22_traceSegment_069_0000_0072, g32p_row22_traceSegment_069_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 144 9 9, g32p_row22_traceSegment_069_0144_0009, g32p_row22_traceSegment_069_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 162 9 9, g32p_row22_traceSegment_069_0162_0009, g32p_row22_traceSegment_069_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 144 18 18, g32p_row22_traceSegment_069_0144_0018, g32p_row22_traceSegment_069_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 180 9 9, g32p_row22_traceSegment_069_0180_0009, g32p_row22_traceSegment_069_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 198 9 9, g32p_row22_traceSegment_069_0198_0009, g32p_row22_traceSegment_069_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 180 18 18, g32p_row22_traceSegment_069_0180_0018, g32p_row22_traceSegment_069_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 144 36 36, g32p_row22_traceSegment_069_0144_0036, g32p_row22_traceSegment_069_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 216 9 9, g32p_row22_traceSegment_069_0216_0009, g32p_row22_traceSegment_069_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 234 9 9, g32p_row22_traceSegment_069_0234_0009, g32p_row22_traceSegment_069_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 216 18 18, g32p_row22_traceSegment_069_0216_0018, g32p_row22_traceSegment_069_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 261 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 252 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 252 9 9, g32p_row22_traceSegment_069_0252_0009, g32p_row22_traceSegment_069_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 270 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 279 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 270 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 270 9 9, g32p_row22_traceSegment_069_0270_0009, g32p_row22_traceSegment_069_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 252 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 252 18 18, g32p_row22_traceSegment_069_0252_0018, g32p_row22_traceSegment_069_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 216 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 216 36 36, g32p_row22_traceSegment_069_0216_0036, g32p_row22_traceSegment_069_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_069 144 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 144 72 72, g32p_row22_traceSegment_069_0144_0072, g32p_row22_traceSegment_069_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_069 0 288 = [2, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 0 144 144, g32p_row22_traceSegment_069_0000_0144, g32p_row22_traceSegment_069_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 288 9 = [2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 297 9 = [3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 288 18 = [5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 288 9 9, g32p_row22_traceSegment_069_0288_0009, g32p_row22_traceSegment_069_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 306 9 = [1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 315 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 306 18 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 306 9 9, g32p_row22_traceSegment_069_0306_0009, g32p_row22_traceSegment_069_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 288 36 = [7, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 288 18 18, g32p_row22_traceSegment_069_0288_0018, g32p_row22_traceSegment_069_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 324 9 = [3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 333 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 324 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 324 9 9, g32p_row22_traceSegment_069_0324_0009, g32p_row22_traceSegment_069_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 351 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 342 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 342 9 9, g32p_row22_traceSegment_069_0342_0009, g32p_row22_traceSegment_069_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 324 36 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 324 18 18, g32p_row22_traceSegment_069_0324_0018, g32p_row22_traceSegment_069_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 288 72 = [11, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 288 36 36, g32p_row22_traceSegment_069_0288_0036, g32p_row22_traceSegment_069_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 360 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 360 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 360 9 9, g32p_row22_traceSegment_069_0360_0009, g32p_row22_traceSegment_069_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 378 9 9, g32p_row22_traceSegment_069_0378_0009, g32p_row22_traceSegment_069_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 360 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 360 18 18, g32p_row22_traceSegment_069_0360_0018, g32p_row22_traceSegment_069_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 396 9 9, g32p_row22_traceSegment_069_0396_0009, g32p_row22_traceSegment_069_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 414 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 414 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 414 9 9, g32p_row22_traceSegment_069_0414_0009, g32p_row22_traceSegment_069_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 396 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 396 18 18, g32p_row22_traceSegment_069_0396_0018, g32p_row22_traceSegment_069_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 360 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 360 36 36, g32p_row22_traceSegment_069_0360_0036, g32p_row22_traceSegment_069_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_069 288 144 = [13, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 288 72 72, g32p_row22_traceSegment_069_0288_0072, g32p_row22_traceSegment_069_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 432 9 = [2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 432 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 432 9 9, g32p_row22_traceSegment_069_0432_0009, g32p_row22_traceSegment_069_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 450 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 450 9 9, g32p_row22_traceSegment_069_0450_0009, g32p_row22_traceSegment_069_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 432 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 432 18 18, g32p_row22_traceSegment_069_0432_0018, g32p_row22_traceSegment_069_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 468 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 477 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 468 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 468 9 9, g32p_row22_traceSegment_069_0468_0009, g32p_row22_traceSegment_069_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 495 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 486 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 486 9 9, g32p_row22_traceSegment_069_0486_0009, g32p_row22_traceSegment_069_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 468 36 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 468 18 18, g32p_row22_traceSegment_069_0468_0018, g32p_row22_traceSegment_069_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 432 72 = [3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 432 36 36, g32p_row22_traceSegment_069_0432_0036, g32p_row22_traceSegment_069_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 513 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 504 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 504 9 9, g32p_row22_traceSegment_069_0504_0009, g32p_row22_traceSegment_069_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 522 9 9, g32p_row22_traceSegment_069_0522_0009, g32p_row22_traceSegment_069_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 504 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 504 18 18, g32p_row22_traceSegment_069_0504_0018, g32p_row22_traceSegment_069_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 540 9 9, g32p_row22_traceSegment_069_0540_0009, g32p_row22_traceSegment_069_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_069 567 9 = [2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_069_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_069 558 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 558 9 9, g32p_row22_traceSegment_069_0558_0009, g32p_row22_traceSegment_069_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_069 540 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 540 18 18, g32p_row22_traceSegment_069_0540_0018, g32p_row22_traceSegment_069_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_069 504 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 504 36 36, g32p_row22_traceSegment_069_0504_0036, g32p_row22_traceSegment_069_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_069 432 144 = [5, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 432 72 72, g32p_row22_traceSegment_069_0432_0072, g32p_row22_traceSegment_069_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_069 288 288 = [18, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 288 144 144, g32p_row22_traceSegment_069_0288_0144, g32p_row22_traceSegment_069_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_069_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_069 0 576 = [20, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_069 0 288 288, g32p_row22_traceSegment_069_0000_0288, g32p_row22_traceSegment_069_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 69 = [20, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_069_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_074 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 74 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_074_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 0 9 9, g32p_row22_traceSegment_074_0000_0009, g32p_row22_traceSegment_074_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 18 9 9, g32p_row22_traceSegment_074_0018_0009, g32p_row22_traceSegment_074_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 0 18 18, g32p_row22_traceSegment_074_0000_0018, g32p_row22_traceSegment_074_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 36 9 9, g32p_row22_traceSegment_074_0036_0009, g32p_row22_traceSegment_074_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 63 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 54 9 9, g32p_row22_traceSegment_074_0054_0009, g32p_row22_traceSegment_074_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 36 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 36 18 18, g32p_row22_traceSegment_074_0036_0018, g32p_row22_traceSegment_074_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 0 36 36, g32p_row22_traceSegment_074_0000_0036, g32p_row22_traceSegment_074_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 81 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 72 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 72 9 9, g32p_row22_traceSegment_074_0072_0009, g32p_row22_traceSegment_074_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 90 9 9, g32p_row22_traceSegment_074_0090_0009, g32p_row22_traceSegment_074_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 72 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 72 18 18, g32p_row22_traceSegment_074_0072_0018, g32p_row22_traceSegment_074_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 117 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 108 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 108 9 9, g32p_row22_traceSegment_074_0108_0009, g32p_row22_traceSegment_074_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 126 9 9, g32p_row22_traceSegment_074_0126_0009, g32p_row22_traceSegment_074_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 108 18 18, g32p_row22_traceSegment_074_0108_0018, g32p_row22_traceSegment_074_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 72 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 72 36 36, g32p_row22_traceSegment_074_0072_0036, g32p_row22_traceSegment_074_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_074 0 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 0 72 72, g32p_row22_traceSegment_074_0000_0072, g32p_row22_traceSegment_074_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 144 9 9, g32p_row22_traceSegment_074_0144_0009, g32p_row22_traceSegment_074_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 162 9 9, g32p_row22_traceSegment_074_0162_0009, g32p_row22_traceSegment_074_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 144 18 18, g32p_row22_traceSegment_074_0144_0018, g32p_row22_traceSegment_074_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 180 9 9, g32p_row22_traceSegment_074_0180_0009, g32p_row22_traceSegment_074_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 198 9 9, g32p_row22_traceSegment_074_0198_0009, g32p_row22_traceSegment_074_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 180 18 18, g32p_row22_traceSegment_074_0180_0018, g32p_row22_traceSegment_074_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 144 36 36, g32p_row22_traceSegment_074_0144_0036, g32p_row22_traceSegment_074_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 216 9 9, g32p_row22_traceSegment_074_0216_0009, g32p_row22_traceSegment_074_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 243 9 = [2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 234 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 234 9 9, g32p_row22_traceSegment_074_0234_0009, g32p_row22_traceSegment_074_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 216 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 216 18 18, g32p_row22_traceSegment_074_0216_0018, g32p_row22_traceSegment_074_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 261 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 252 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 252 9 9, g32p_row22_traceSegment_074_0252_0009, g32p_row22_traceSegment_074_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 270 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 270 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 270 9 9, g32p_row22_traceSegment_074_0270_0009, g32p_row22_traceSegment_074_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 252 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 252 18 18, g32p_row22_traceSegment_074_0252_0018, g32p_row22_traceSegment_074_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 216 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 216 36 36, g32p_row22_traceSegment_074_0216_0036, g32p_row22_traceSegment_074_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_074 144 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 144 72 72, g32p_row22_traceSegment_074_0144_0072, g32p_row22_traceSegment_074_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_074 0 288 = [7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 0 144 144, g32p_row22_traceSegment_074_0000_0144, g32p_row22_traceSegment_074_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 288 9 9, g32p_row22_traceSegment_074_0288_0009, g32p_row22_traceSegment_074_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 306 9 9, g32p_row22_traceSegment_074_0306_0009, g32p_row22_traceSegment_074_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 288 18 18, g32p_row22_traceSegment_074_0288_0018, g32p_row22_traceSegment_074_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 324 9 9, g32p_row22_traceSegment_074_0324_0009, g32p_row22_traceSegment_074_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 342 9 9, g32p_row22_traceSegment_074_0342_0009, g32p_row22_traceSegment_074_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 324 18 18, g32p_row22_traceSegment_074_0324_0018, g32p_row22_traceSegment_074_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 288 36 36, g32p_row22_traceSegment_074_0288_0036, g32p_row22_traceSegment_074_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 360 9 9, g32p_row22_traceSegment_074_0360_0009, g32p_row22_traceSegment_074_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 378 9 9, g32p_row22_traceSegment_074_0378_0009, g32p_row22_traceSegment_074_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 360 18 18, g32p_row22_traceSegment_074_0360_0018, g32p_row22_traceSegment_074_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 396 9 9, g32p_row22_traceSegment_074_0396_0009, g32p_row22_traceSegment_074_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 414 9 9, g32p_row22_traceSegment_074_0414_0009, g32p_row22_traceSegment_074_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 396 18 18, g32p_row22_traceSegment_074_0396_0018, g32p_row22_traceSegment_074_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 360 36 36, g32p_row22_traceSegment_074_0360_0036, g32p_row22_traceSegment_074_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_074 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 288 72 72, g32p_row22_traceSegment_074_0288_0072, g32p_row22_traceSegment_074_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 432 9 9, g32p_row22_traceSegment_074_0432_0009, g32p_row22_traceSegment_074_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 450 9 9, g32p_row22_traceSegment_074_0450_0009, g32p_row22_traceSegment_074_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 432 18 18, g32p_row22_traceSegment_074_0432_0018, g32p_row22_traceSegment_074_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 468 9 9, g32p_row22_traceSegment_074_0468_0009, g32p_row22_traceSegment_074_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 486 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 495 9 = [3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 486 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 486 9 9, g32p_row22_traceSegment_074_0486_0009, g32p_row22_traceSegment_074_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 468 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 468 18 18, g32p_row22_traceSegment_074_0468_0018, g32p_row22_traceSegment_074_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 432 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 432 36 36, g32p_row22_traceSegment_074_0432_0036, g32p_row22_traceSegment_074_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 513 9 = [4] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 504 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 504 9 9, g32p_row22_traceSegment_074_0504_0009, g32p_row22_traceSegment_074_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 531 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 522 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 522 9 9, g32p_row22_traceSegment_074_0522_0009, g32p_row22_traceSegment_074_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 504 36 = [5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 504 18 18, g32p_row22_traceSegment_074_0504_0018, g32p_row22_traceSegment_074_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 540 9 9, g32p_row22_traceSegment_074_0540_0009, g32p_row22_traceSegment_074_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_074 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_074_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_074 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 558 9 9, g32p_row22_traceSegment_074_0558_0009, g32p_row22_traceSegment_074_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_074 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 540 18 18, g32p_row22_traceSegment_074_0540_0018, g32p_row22_traceSegment_074_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_074 504 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 504 36 36, g32p_row22_traceSegment_074_0504_0036, g32p_row22_traceSegment_074_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_074 432 144 = [9] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 432 72 72, g32p_row22_traceSegment_074_0432_0072, g32p_row22_traceSegment_074_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_074 288 288 = [9] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 288 144 144, g32p_row22_traceSegment_074_0288_0144, g32p_row22_traceSegment_074_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_074_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_074 0 576 = [16] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_074 0 288 288, g32p_row22_traceSegment_074_0000_0288, g32p_row22_traceSegment_074_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 74 = [16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_074_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_078_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 0 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 0 9 9, g32p_row22_traceSegment_078_0000_0009, g32p_row22_traceSegment_078_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 18 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 18 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 18 9 9, g32p_row22_traceSegment_078_0018_0009, g32p_row22_traceSegment_078_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 0 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 0 18 18, g32p_row22_traceSegment_078_0000_0018, g32p_row22_traceSegment_078_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 36 9 9, g32p_row22_traceSegment_078_0036_0009, g32p_row22_traceSegment_078_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 54 9 9, g32p_row22_traceSegment_078_0054_0009, g32p_row22_traceSegment_078_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 36 18 18, g32p_row22_traceSegment_078_0036_0018, g32p_row22_traceSegment_078_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 0 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 0 36 36, g32p_row22_traceSegment_078_0000_0036, g32p_row22_traceSegment_078_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 72 9 9, g32p_row22_traceSegment_078_0072_0009, g32p_row22_traceSegment_078_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 90 9 9, g32p_row22_traceSegment_078_0090_0009, g32p_row22_traceSegment_078_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 72 18 18, g32p_row22_traceSegment_078_0072_0018, g32p_row22_traceSegment_078_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 108 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 117 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 108 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 108 9 9, g32p_row22_traceSegment_078_0108_0009, g32p_row22_traceSegment_078_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 126 9 9, g32p_row22_traceSegment_078_0126_0009, g32p_row22_traceSegment_078_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 108 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 108 18 18, g32p_row22_traceSegment_078_0108_0018, g32p_row22_traceSegment_078_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 72 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 72 36 36, g32p_row22_traceSegment_078_0072_0036, g32p_row22_traceSegment_078_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_078 0 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 0 72 72, g32p_row22_traceSegment_078_0000_0072, g32p_row22_traceSegment_078_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 144 9 9, g32p_row22_traceSegment_078_0144_0009, g32p_row22_traceSegment_078_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 162 9 9, g32p_row22_traceSegment_078_0162_0009, g32p_row22_traceSegment_078_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 144 18 18, g32p_row22_traceSegment_078_0144_0018, g32p_row22_traceSegment_078_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 180 9 9, g32p_row22_traceSegment_078_0180_0009, g32p_row22_traceSegment_078_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 198 9 9, g32p_row22_traceSegment_078_0198_0009, g32p_row22_traceSegment_078_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 180 18 18, g32p_row22_traceSegment_078_0180_0018, g32p_row22_traceSegment_078_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 144 36 36, g32p_row22_traceSegment_078_0144_0036, g32p_row22_traceSegment_078_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 216 9 9, g32p_row22_traceSegment_078_0216_0009, g32p_row22_traceSegment_078_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 234 9 = [3] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 234 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 234 9 9, g32p_row22_traceSegment_078_0234_0009, g32p_row22_traceSegment_078_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 216 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 216 18 18, g32p_row22_traceSegment_078_0216_0018, g32p_row22_traceSegment_078_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 252 9 9, g32p_row22_traceSegment_078_0252_0009, g32p_row22_traceSegment_078_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 270 9 9, g32p_row22_traceSegment_078_0270_0009, g32p_row22_traceSegment_078_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 252 18 18, g32p_row22_traceSegment_078_0252_0018, g32p_row22_traceSegment_078_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 216 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 216 36 36, g32p_row22_traceSegment_078_0216_0036, g32p_row22_traceSegment_078_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_078 144 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 144 72 72, g32p_row22_traceSegment_078_0144_0072, g32p_row22_traceSegment_078_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_078 0 288 = [7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 0 144 144, g32p_row22_traceSegment_078_0000_0144, g32p_row22_traceSegment_078_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 288 9 9, g32p_row22_traceSegment_078_0288_0009, g32p_row22_traceSegment_078_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 306 9 9, g32p_row22_traceSegment_078_0306_0009, g32p_row22_traceSegment_078_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 288 18 18, g32p_row22_traceSegment_078_0288_0018, g32p_row22_traceSegment_078_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 324 9 9, g32p_row22_traceSegment_078_0324_0009, g32p_row22_traceSegment_078_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 342 9 9, g32p_row22_traceSegment_078_0342_0009, g32p_row22_traceSegment_078_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 324 18 18, g32p_row22_traceSegment_078_0324_0018, g32p_row22_traceSegment_078_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 288 36 36, g32p_row22_traceSegment_078_0288_0036, g32p_row22_traceSegment_078_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 360 9 9, g32p_row22_traceSegment_078_0360_0009, g32p_row22_traceSegment_078_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 378 9 9, g32p_row22_traceSegment_078_0378_0009, g32p_row22_traceSegment_078_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 360 18 18, g32p_row22_traceSegment_078_0360_0018, g32p_row22_traceSegment_078_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 396 9 9, g32p_row22_traceSegment_078_0396_0009, g32p_row22_traceSegment_078_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 414 9 9, g32p_row22_traceSegment_078_0414_0009, g32p_row22_traceSegment_078_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 396 18 18, g32p_row22_traceSegment_078_0396_0018, g32p_row22_traceSegment_078_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 360 36 36, g32p_row22_traceSegment_078_0360_0036, g32p_row22_traceSegment_078_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_078 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 288 72 72, g32p_row22_traceSegment_078_0288_0072, g32p_row22_traceSegment_078_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 432 9 9, g32p_row22_traceSegment_078_0432_0009, g32p_row22_traceSegment_078_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 450 9 9, g32p_row22_traceSegment_078_0450_0009, g32p_row22_traceSegment_078_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 432 18 18, g32p_row22_traceSegment_078_0432_0018, g32p_row22_traceSegment_078_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 468 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 468 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 468 9 9, g32p_row22_traceSegment_078_0468_0009, g32p_row22_traceSegment_078_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 486 9 9, g32p_row22_traceSegment_078_0486_0009, g32p_row22_traceSegment_078_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 468 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 468 18 18, g32p_row22_traceSegment_078_0468_0018, g32p_row22_traceSegment_078_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 432 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 432 36 36, g32p_row22_traceSegment_078_0432_0036, g32p_row22_traceSegment_078_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 504 9 9, g32p_row22_traceSegment_078_0504_0009, g32p_row22_traceSegment_078_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 522 9 9, g32p_row22_traceSegment_078_0522_0009, g32p_row22_traceSegment_078_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 504 18 18, g32p_row22_traceSegment_078_0504_0018, g32p_row22_traceSegment_078_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 540 9 9, g32p_row22_traceSegment_078_0540_0009, g32p_row22_traceSegment_078_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_078 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_078_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_078 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 558 9 9, g32p_row22_traceSegment_078_0558_0009, g32p_row22_traceSegment_078_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_078 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 540 18 18, g32p_row22_traceSegment_078_0540_0018, g32p_row22_traceSegment_078_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_078 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 504 36 36, g32p_row22_traceSegment_078_0504_0036, g32p_row22_traceSegment_078_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_078 432 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 432 72 72, g32p_row22_traceSegment_078_0432_0072, g32p_row22_traceSegment_078_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_078 288 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 288 144 144, g32p_row22_traceSegment_078_0288_0144, g32p_row22_traceSegment_078_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_078_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_078 0 576 = [8] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_078 0 288 288, g32p_row22_traceSegment_078_0000_0288, g32p_row22_traceSegment_078_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 78 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_078_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_082_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 0 9 9, g32p_row22_traceSegment_082_0000_0009, g32p_row22_traceSegment_082_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 18 9 9, g32p_row22_traceSegment_082_0018_0009, g32p_row22_traceSegment_082_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 0 18 18, g32p_row22_traceSegment_082_0000_0018, g32p_row22_traceSegment_082_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 36 9 9, g32p_row22_traceSegment_082_0036_0009, g32p_row22_traceSegment_082_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 54 9 9, g32p_row22_traceSegment_082_0054_0009, g32p_row22_traceSegment_082_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 36 18 18, g32p_row22_traceSegment_082_0036_0018, g32p_row22_traceSegment_082_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 0 36 36, g32p_row22_traceSegment_082_0000_0036, g32p_row22_traceSegment_082_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 72 9 9, g32p_row22_traceSegment_082_0072_0009, g32p_row22_traceSegment_082_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 90 9 9, g32p_row22_traceSegment_082_0090_0009, g32p_row22_traceSegment_082_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 72 18 18, g32p_row22_traceSegment_082_0072_0018, g32p_row22_traceSegment_082_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 108 9 9, g32p_row22_traceSegment_082_0108_0009, g32p_row22_traceSegment_082_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 135 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 126 9 9, g32p_row22_traceSegment_082_0126_0009, g32p_row22_traceSegment_082_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 108 18 18, g32p_row22_traceSegment_082_0108_0018, g32p_row22_traceSegment_082_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 72 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 72 36 36, g32p_row22_traceSegment_082_0072_0036, g32p_row22_traceSegment_082_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_082 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 0 72 72, g32p_row22_traceSegment_082_0000_0072, g32p_row22_traceSegment_082_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 153 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 144 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 144 9 9, g32p_row22_traceSegment_082_0144_0009, g32p_row22_traceSegment_082_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 162 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 171 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 162 18 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 162 9 9, g32p_row22_traceSegment_082_0162_0009, g32p_row22_traceSegment_082_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 144 36 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 144 18 18, g32p_row22_traceSegment_082_0144_0018, g32p_row22_traceSegment_082_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 180 9 9, g32p_row22_traceSegment_082_0180_0009, g32p_row22_traceSegment_082_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 198 9 9, g32p_row22_traceSegment_082_0198_0009, g32p_row22_traceSegment_082_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 180 18 18, g32p_row22_traceSegment_082_0180_0018, g32p_row22_traceSegment_082_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 144 72 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 144 36 36, g32p_row22_traceSegment_082_0144_0036, g32p_row22_traceSegment_082_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 216 9 9, g32p_row22_traceSegment_082_0216_0009, g32p_row22_traceSegment_082_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 234 9 9, g32p_row22_traceSegment_082_0234_0009, g32p_row22_traceSegment_082_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 216 18 18, g32p_row22_traceSegment_082_0216_0018, g32p_row22_traceSegment_082_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 252 9 9, g32p_row22_traceSegment_082_0252_0009, g32p_row22_traceSegment_082_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 270 9 9, g32p_row22_traceSegment_082_0270_0009, g32p_row22_traceSegment_082_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 252 18 18, g32p_row22_traceSegment_082_0252_0018, g32p_row22_traceSegment_082_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 216 36 36, g32p_row22_traceSegment_082_0216_0036, g32p_row22_traceSegment_082_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_082 144 144 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 144 72 72, g32p_row22_traceSegment_082_0144_0072, g32p_row22_traceSegment_082_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_082 0 288 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 0 144 144, g32p_row22_traceSegment_082_0000_0144, g32p_row22_traceSegment_082_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 288 9 9, g32p_row22_traceSegment_082_0288_0009, g32p_row22_traceSegment_082_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 306 9 9, g32p_row22_traceSegment_082_0306_0009, g32p_row22_traceSegment_082_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 288 18 18, g32p_row22_traceSegment_082_0288_0018, g32p_row22_traceSegment_082_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 324 9 9, g32p_row22_traceSegment_082_0324_0009, g32p_row22_traceSegment_082_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 342 9 9, g32p_row22_traceSegment_082_0342_0009, g32p_row22_traceSegment_082_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 324 18 18, g32p_row22_traceSegment_082_0324_0018, g32p_row22_traceSegment_082_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 288 36 36, g32p_row22_traceSegment_082_0288_0036, g32p_row22_traceSegment_082_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 360 9 9, g32p_row22_traceSegment_082_0360_0009, g32p_row22_traceSegment_082_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 378 9 9, g32p_row22_traceSegment_082_0378_0009, g32p_row22_traceSegment_082_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 360 18 18, g32p_row22_traceSegment_082_0360_0018, g32p_row22_traceSegment_082_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 396 9 9, g32p_row22_traceSegment_082_0396_0009, g32p_row22_traceSegment_082_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 414 9 9, g32p_row22_traceSegment_082_0414_0009, g32p_row22_traceSegment_082_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 396 18 18, g32p_row22_traceSegment_082_0396_0018, g32p_row22_traceSegment_082_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 360 36 36, g32p_row22_traceSegment_082_0360_0036, g32p_row22_traceSegment_082_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_082 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 288 72 72, g32p_row22_traceSegment_082_0288_0072, g32p_row22_traceSegment_082_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 432 9 9, g32p_row22_traceSegment_082_0432_0009, g32p_row22_traceSegment_082_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 450 9 9, g32p_row22_traceSegment_082_0450_0009, g32p_row22_traceSegment_082_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 432 18 18, g32p_row22_traceSegment_082_0432_0018, g32p_row22_traceSegment_082_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 468 9 9, g32p_row22_traceSegment_082_0468_0009, g32p_row22_traceSegment_082_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 486 9 9, g32p_row22_traceSegment_082_0486_0009, g32p_row22_traceSegment_082_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 468 18 18, g32p_row22_traceSegment_082_0468_0018, g32p_row22_traceSegment_082_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 432 36 36, g32p_row22_traceSegment_082_0432_0036, g32p_row22_traceSegment_082_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 504 9 9, g32p_row22_traceSegment_082_0504_0009, g32p_row22_traceSegment_082_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 531 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 522 9 9, g32p_row22_traceSegment_082_0522_0009, g32p_row22_traceSegment_082_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 504 18 18, g32p_row22_traceSegment_082_0504_0018, g32p_row22_traceSegment_082_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 540 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 540 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 540 9 9, g32p_row22_traceSegment_082_0540_0009, g32p_row22_traceSegment_082_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_082 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_082_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_082 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 558 9 9, g32p_row22_traceSegment_082_0558_0009, g32p_row22_traceSegment_082_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_082 540 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 540 18 18, g32p_row22_traceSegment_082_0540_0018, g32p_row22_traceSegment_082_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_082 504 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 504 36 36, g32p_row22_traceSegment_082_0504_0036, g32p_row22_traceSegment_082_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_082 432 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 432 72 72, g32p_row22_traceSegment_082_0432_0072, g32p_row22_traceSegment_082_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_082 288 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 288 144 144, g32p_row22_traceSegment_082_0288_0144, g32p_row22_traceSegment_082_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_082_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_082 0 576 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_082 0 288 288, g32p_row22_traceSegment_082_0000_0288, g32p_row22_traceSegment_082_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 82 = [0, 0, 10] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_082_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_083 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 83 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_083_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 0 9 9, g32p_row22_traceSegment_083_0000_0009, g32p_row22_traceSegment_083_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 27 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 18 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 18 9 9, g32p_row22_traceSegment_083_0018_0009, g32p_row22_traceSegment_083_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 0 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 0 18 18, g32p_row22_traceSegment_083_0000_0018, g32p_row22_traceSegment_083_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 45 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 36 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 36 9 9, g32p_row22_traceSegment_083_0036_0009, g32p_row22_traceSegment_083_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 54 9 9, g32p_row22_traceSegment_083_0054_0009, g32p_row22_traceSegment_083_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 36 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 36 18 18, g32p_row22_traceSegment_083_0036_0018, g32p_row22_traceSegment_083_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 0 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 0 36 36, g32p_row22_traceSegment_083_0000_0036, g32p_row22_traceSegment_083_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 72 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 72 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 72 9 9, g32p_row22_traceSegment_083_0072_0009, g32p_row22_traceSegment_083_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 90 9 9, g32p_row22_traceSegment_083_0090_0009, g32p_row22_traceSegment_083_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 72 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 72 18 18, g32p_row22_traceSegment_083_0072_0018, g32p_row22_traceSegment_083_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 108 9 9, g32p_row22_traceSegment_083_0108_0009, g32p_row22_traceSegment_083_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 126 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 126 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 126 9 9, g32p_row22_traceSegment_083_0126_0009, g32p_row22_traceSegment_083_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 108 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 108 18 18, g32p_row22_traceSegment_083_0108_0018, g32p_row22_traceSegment_083_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 72 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 72 36 36, g32p_row22_traceSegment_083_0072_0036, g32p_row22_traceSegment_083_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_083 0 144 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 0 72 72, g32p_row22_traceSegment_083_0000_0072, g32p_row22_traceSegment_083_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 144 9 9, g32p_row22_traceSegment_083_0144_0009, g32p_row22_traceSegment_083_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 162 9 9, g32p_row22_traceSegment_083_0162_0009, g32p_row22_traceSegment_083_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 144 18 18, g32p_row22_traceSegment_083_0144_0018, g32p_row22_traceSegment_083_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 180 9 9, g32p_row22_traceSegment_083_0180_0009, g32p_row22_traceSegment_083_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 198 9 9, g32p_row22_traceSegment_083_0198_0009, g32p_row22_traceSegment_083_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 180 18 18, g32p_row22_traceSegment_083_0180_0018, g32p_row22_traceSegment_083_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 144 36 36, g32p_row22_traceSegment_083_0144_0036, g32p_row22_traceSegment_083_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 216 9 9, g32p_row22_traceSegment_083_0216_0009, g32p_row22_traceSegment_083_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 234 9 9, g32p_row22_traceSegment_083_0234_0009, g32p_row22_traceSegment_083_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 216 18 18, g32p_row22_traceSegment_083_0216_0018, g32p_row22_traceSegment_083_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 252 9 9, g32p_row22_traceSegment_083_0252_0009, g32p_row22_traceSegment_083_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 279 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 270 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 270 9 9, g32p_row22_traceSegment_083_0270_0009, g32p_row22_traceSegment_083_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 252 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 252 18 18, g32p_row22_traceSegment_083_0252_0018, g32p_row22_traceSegment_083_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 216 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 216 36 36, g32p_row22_traceSegment_083_0216_0036, g32p_row22_traceSegment_083_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_083 144 144 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 144 72 72, g32p_row22_traceSegment_083_0144_0072, g32p_row22_traceSegment_083_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_083 0 288 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 0 144 144, g32p_row22_traceSegment_083_0000_0144, g32p_row22_traceSegment_083_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 288 9 9, g32p_row22_traceSegment_083_0288_0009, g32p_row22_traceSegment_083_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 306 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 315 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 306 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 306 9 9, g32p_row22_traceSegment_083_0306_0009, g32p_row22_traceSegment_083_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 288 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 288 18 18, g32p_row22_traceSegment_083_0288_0018, g32p_row22_traceSegment_083_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 333 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 324 9 9, g32p_row22_traceSegment_083_0324_0009, g32p_row22_traceSegment_083_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 342 9 9, g32p_row22_traceSegment_083_0342_0009, g32p_row22_traceSegment_083_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 324 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 324 18 18, g32p_row22_traceSegment_083_0324_0018, g32p_row22_traceSegment_083_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 288 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 288 36 36, g32p_row22_traceSegment_083_0288_0036, g32p_row22_traceSegment_083_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 360 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 360 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 360 9 9, g32p_row22_traceSegment_083_0360_0009, g32p_row22_traceSegment_083_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 378 9 9, g32p_row22_traceSegment_083_0378_0009, g32p_row22_traceSegment_083_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 360 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 360 18 18, g32p_row22_traceSegment_083_0360_0018, g32p_row22_traceSegment_083_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 396 9 9, g32p_row22_traceSegment_083_0396_0009, g32p_row22_traceSegment_083_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 414 9 9, g32p_row22_traceSegment_083_0414_0009, g32p_row22_traceSegment_083_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 396 18 18, g32p_row22_traceSegment_083_0396_0018, g32p_row22_traceSegment_083_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 360 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 360 36 36, g32p_row22_traceSegment_083_0360_0036, g32p_row22_traceSegment_083_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_083 288 144 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 288 72 72, g32p_row22_traceSegment_083_0288_0072, g32p_row22_traceSegment_083_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 432 9 9, g32p_row22_traceSegment_083_0432_0009, g32p_row22_traceSegment_083_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 450 9 9, g32p_row22_traceSegment_083_0450_0009, g32p_row22_traceSegment_083_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 432 18 18, g32p_row22_traceSegment_083_0432_0018, g32p_row22_traceSegment_083_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 468 9 9, g32p_row22_traceSegment_083_0468_0009, g32p_row22_traceSegment_083_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 486 9 9, g32p_row22_traceSegment_083_0486_0009, g32p_row22_traceSegment_083_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 468 18 18, g32p_row22_traceSegment_083_0468_0018, g32p_row22_traceSegment_083_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 432 36 36, g32p_row22_traceSegment_083_0432_0036, g32p_row22_traceSegment_083_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 504 9 9, g32p_row22_traceSegment_083_0504_0009, g32p_row22_traceSegment_083_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 531 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 522 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 522 9 9, g32p_row22_traceSegment_083_0522_0009, g32p_row22_traceSegment_083_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 504 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 504 18 18, g32p_row22_traceSegment_083_0504_0018, g32p_row22_traceSegment_083_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 549 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 540 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 540 9 9, g32p_row22_traceSegment_083_0540_0009, g32p_row22_traceSegment_083_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_083 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_083_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_083 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 558 9 9, g32p_row22_traceSegment_083_0558_0009, g32p_row22_traceSegment_083_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_083 540 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 540 18 18, g32p_row22_traceSegment_083_0540_0018, g32p_row22_traceSegment_083_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_083 504 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 504 36 36, g32p_row22_traceSegment_083_0504_0036, g32p_row22_traceSegment_083_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_083 432 144 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 432 72 72, g32p_row22_traceSegment_083_0432_0072, g32p_row22_traceSegment_083_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_083 288 288 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 288 144 144, g32p_row22_traceSegment_083_0288_0144, g32p_row22_traceSegment_083_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_083_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_083 0 576 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_083 0 288 288, g32p_row22_traceSegment_083_0000_0288, g32p_row22_traceSegment_083_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 83 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_083_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_090 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 90 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_090_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 0 9 9, g32p_row22_traceSegment_090_0000_0009, g32p_row22_traceSegment_090_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 18 9 9, g32p_row22_traceSegment_090_0018_0009, g32p_row22_traceSegment_090_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 0 18 18, g32p_row22_traceSegment_090_0000_0018, g32p_row22_traceSegment_090_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 36 9 9, g32p_row22_traceSegment_090_0036_0009, g32p_row22_traceSegment_090_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 54 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 54 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 54 9 9, g32p_row22_traceSegment_090_0054_0009, g32p_row22_traceSegment_090_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 36 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 36 18 18, g32p_row22_traceSegment_090_0036_0018, g32p_row22_traceSegment_090_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 0 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 0 36 36, g32p_row22_traceSegment_090_0000_0036, g32p_row22_traceSegment_090_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 72 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 72 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 72 9 9, g32p_row22_traceSegment_090_0072_0009, g32p_row22_traceSegment_090_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 90 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 90 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 90 9 9, g32p_row22_traceSegment_090_0090_0009, g32p_row22_traceSegment_090_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 72 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 72 18 18, g32p_row22_traceSegment_090_0072_0018, g32p_row22_traceSegment_090_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 108 9 9, g32p_row22_traceSegment_090_0108_0009, g32p_row22_traceSegment_090_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 126 9 9, g32p_row22_traceSegment_090_0126_0009, g32p_row22_traceSegment_090_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 108 18 18, g32p_row22_traceSegment_090_0108_0018, g32p_row22_traceSegment_090_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 72 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 72 36 36, g32p_row22_traceSegment_090_0072_0036, g32p_row22_traceSegment_090_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_090 0 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 0 72 72, g32p_row22_traceSegment_090_0000_0072, g32p_row22_traceSegment_090_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 144 9 9, g32p_row22_traceSegment_090_0144_0009, g32p_row22_traceSegment_090_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 162 9 9, g32p_row22_traceSegment_090_0162_0009, g32p_row22_traceSegment_090_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 144 18 18, g32p_row22_traceSegment_090_0144_0018, g32p_row22_traceSegment_090_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 180 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 180 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 180 9 9, g32p_row22_traceSegment_090_0180_0009, g32p_row22_traceSegment_090_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 198 9 9, g32p_row22_traceSegment_090_0198_0009, g32p_row22_traceSegment_090_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 180 18 18, g32p_row22_traceSegment_090_0180_0018, g32p_row22_traceSegment_090_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 144 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 144 36 36, g32p_row22_traceSegment_090_0144_0036, g32p_row22_traceSegment_090_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 216 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 216 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 216 9 9, g32p_row22_traceSegment_090_0216_0009, g32p_row22_traceSegment_090_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 234 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 234 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 234 9 9, g32p_row22_traceSegment_090_0234_0009, g32p_row22_traceSegment_090_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 216 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 216 18 18, g32p_row22_traceSegment_090_0216_0018, g32p_row22_traceSegment_090_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 252 9 9, g32p_row22_traceSegment_090_0252_0009, g32p_row22_traceSegment_090_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 270 9 9, g32p_row22_traceSegment_090_0270_0009, g32p_row22_traceSegment_090_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 252 18 18, g32p_row22_traceSegment_090_0252_0018, g32p_row22_traceSegment_090_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 216 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 216 36 36, g32p_row22_traceSegment_090_0216_0036, g32p_row22_traceSegment_090_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_090 144 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 144 72 72, g32p_row22_traceSegment_090_0144_0072, g32p_row22_traceSegment_090_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_090 0 288 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 0 144 144, g32p_row22_traceSegment_090_0000_0144, g32p_row22_traceSegment_090_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 288 9 9, g32p_row22_traceSegment_090_0288_0009, g32p_row22_traceSegment_090_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 315 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 306 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 306 9 9, g32p_row22_traceSegment_090_0306_0009, g32p_row22_traceSegment_090_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 288 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 288 18 18, g32p_row22_traceSegment_090_0288_0018, g32p_row22_traceSegment_090_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 324 9 9, g32p_row22_traceSegment_090_0324_0009, g32p_row22_traceSegment_090_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 351 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 342 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 342 9 9, g32p_row22_traceSegment_090_0342_0009, g32p_row22_traceSegment_090_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 324 18 18, g32p_row22_traceSegment_090_0324_0018, g32p_row22_traceSegment_090_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 288 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 288 36 36, g32p_row22_traceSegment_090_0288_0036, g32p_row22_traceSegment_090_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 369 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 360 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 360 9 9, g32p_row22_traceSegment_090_0360_0009, g32p_row22_traceSegment_090_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 378 9 9, g32p_row22_traceSegment_090_0378_0009, g32p_row22_traceSegment_090_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 360 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 360 18 18, g32p_row22_traceSegment_090_0360_0018, g32p_row22_traceSegment_090_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 396 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 396 9 9, g32p_row22_traceSegment_090_0396_0009, g32p_row22_traceSegment_090_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 414 9 9, g32p_row22_traceSegment_090_0414_0009, g32p_row22_traceSegment_090_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 396 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 396 18 18, g32p_row22_traceSegment_090_0396_0018, g32p_row22_traceSegment_090_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 360 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 360 36 36, g32p_row22_traceSegment_090_0360_0036, g32p_row22_traceSegment_090_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_090 288 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 288 72 72, g32p_row22_traceSegment_090_0288_0072, g32p_row22_traceSegment_090_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 432 9 9, g32p_row22_traceSegment_090_0432_0009, g32p_row22_traceSegment_090_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 450 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 450 9 9, g32p_row22_traceSegment_090_0450_0009, g32p_row22_traceSegment_090_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 432 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 432 18 18, g32p_row22_traceSegment_090_0432_0018, g32p_row22_traceSegment_090_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 468 9 9, g32p_row22_traceSegment_090_0468_0009, g32p_row22_traceSegment_090_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 486 9 9, g32p_row22_traceSegment_090_0486_0009, g32p_row22_traceSegment_090_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 468 18 18, g32p_row22_traceSegment_090_0468_0018, g32p_row22_traceSegment_090_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 432 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 432 36 36, g32p_row22_traceSegment_090_0432_0036, g32p_row22_traceSegment_090_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 504 9 9, g32p_row22_traceSegment_090_0504_0009, g32p_row22_traceSegment_090_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 522 9 9, g32p_row22_traceSegment_090_0522_0009, g32p_row22_traceSegment_090_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 504 18 18, g32p_row22_traceSegment_090_0504_0018, g32p_row22_traceSegment_090_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 540 9 9, g32p_row22_traceSegment_090_0540_0009, g32p_row22_traceSegment_090_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_090 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_090_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_090 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 558 9 9, g32p_row22_traceSegment_090_0558_0009, g32p_row22_traceSegment_090_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_090 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 540 18 18, g32p_row22_traceSegment_090_0540_0018, g32p_row22_traceSegment_090_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_090 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 504 36 36, g32p_row22_traceSegment_090_0504_0036, g32p_row22_traceSegment_090_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_090 432 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 432 72 72, g32p_row22_traceSegment_090_0432_0072, g32p_row22_traceSegment_090_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_090 288 288 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 288 144 144, g32p_row22_traceSegment_090_0288_0144, g32p_row22_traceSegment_090_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_090_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_090 0 576 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_090 0 288 288, g32p_row22_traceSegment_090_0000_0288, g32p_row22_traceSegment_090_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 90 = [0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_090_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_092_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 0 9 9, g32p_row22_traceSegment_092_0000_0009, g32p_row22_traceSegment_092_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 18 9 9, g32p_row22_traceSegment_092_0018_0009, g32p_row22_traceSegment_092_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 0 18 18, g32p_row22_traceSegment_092_0000_0018, g32p_row22_traceSegment_092_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 36 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 36 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 36 9 9, g32p_row22_traceSegment_092_0036_0009, g32p_row22_traceSegment_092_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 54 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 54 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 54 9 9, g32p_row22_traceSegment_092_0054_0009, g32p_row22_traceSegment_092_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 36 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 36 18 18, g32p_row22_traceSegment_092_0036_0018, g32p_row22_traceSegment_092_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 0 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 0 36 36, g32p_row22_traceSegment_092_0000_0036, g32p_row22_traceSegment_092_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 72 9 9, g32p_row22_traceSegment_092_0072_0009, g32p_row22_traceSegment_092_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 90 9 9, g32p_row22_traceSegment_092_0090_0009, g32p_row22_traceSegment_092_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 72 18 18, g32p_row22_traceSegment_092_0072_0018, g32p_row22_traceSegment_092_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 108 9 9, g32p_row22_traceSegment_092_0108_0009, g32p_row22_traceSegment_092_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 135 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 126 9 9, g32p_row22_traceSegment_092_0126_0009, g32p_row22_traceSegment_092_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 108 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 108 18 18, g32p_row22_traceSegment_092_0108_0018, g32p_row22_traceSegment_092_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 72 36 36, g32p_row22_traceSegment_092_0072_0036, g32p_row22_traceSegment_092_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_092 0 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 0 72 72, g32p_row22_traceSegment_092_0000_0072, g32p_row22_traceSegment_092_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 144 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 144 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 144 9 9, g32p_row22_traceSegment_092_0144_0009, g32p_row22_traceSegment_092_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 162 9 9, g32p_row22_traceSegment_092_0162_0009, g32p_row22_traceSegment_092_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 144 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 144 18 18, g32p_row22_traceSegment_092_0144_0018, g32p_row22_traceSegment_092_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 180 9 9, g32p_row22_traceSegment_092_0180_0009, g32p_row22_traceSegment_092_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 198 9 9, g32p_row22_traceSegment_092_0198_0009, g32p_row22_traceSegment_092_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 180 18 18, g32p_row22_traceSegment_092_0180_0018, g32p_row22_traceSegment_092_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 144 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 144 36 36, g32p_row22_traceSegment_092_0144_0036, g32p_row22_traceSegment_092_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 216 9 9, g32p_row22_traceSegment_092_0216_0009, g32p_row22_traceSegment_092_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 243 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 234 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 234 9 9, g32p_row22_traceSegment_092_0234_0009, g32p_row22_traceSegment_092_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 216 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 216 18 18, g32p_row22_traceSegment_092_0216_0018, g32p_row22_traceSegment_092_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 252 9 9, g32p_row22_traceSegment_092_0252_0009, g32p_row22_traceSegment_092_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 270 9 9, g32p_row22_traceSegment_092_0270_0009, g32p_row22_traceSegment_092_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 252 18 18, g32p_row22_traceSegment_092_0252_0018, g32p_row22_traceSegment_092_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 216 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 216 36 36, g32p_row22_traceSegment_092_0216_0036, g32p_row22_traceSegment_092_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_092 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 144 72 72, g32p_row22_traceSegment_092_0144_0072, g32p_row22_traceSegment_092_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_092 0 288 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 0 144 144, g32p_row22_traceSegment_092_0000_0144, g32p_row22_traceSegment_092_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 288 9 9, g32p_row22_traceSegment_092_0288_0009, g32p_row22_traceSegment_092_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 306 9 9, g32p_row22_traceSegment_092_0306_0009, g32p_row22_traceSegment_092_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 288 18 18, g32p_row22_traceSegment_092_0288_0018, g32p_row22_traceSegment_092_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 324 9 9, g32p_row22_traceSegment_092_0324_0009, g32p_row22_traceSegment_092_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 342 9 9, g32p_row22_traceSegment_092_0342_0009, g32p_row22_traceSegment_092_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 324 18 18, g32p_row22_traceSegment_092_0324_0018, g32p_row22_traceSegment_092_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 288 36 36, g32p_row22_traceSegment_092_0288_0036, g32p_row22_traceSegment_092_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 360 9 9, g32p_row22_traceSegment_092_0360_0009, g32p_row22_traceSegment_092_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 378 9 9, g32p_row22_traceSegment_092_0378_0009, g32p_row22_traceSegment_092_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 360 18 18, g32p_row22_traceSegment_092_0360_0018, g32p_row22_traceSegment_092_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 396 9 9, g32p_row22_traceSegment_092_0396_0009, g32p_row22_traceSegment_092_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 414 9 9, g32p_row22_traceSegment_092_0414_0009, g32p_row22_traceSegment_092_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 396 18 18, g32p_row22_traceSegment_092_0396_0018, g32p_row22_traceSegment_092_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 360 36 36, g32p_row22_traceSegment_092_0360_0036, g32p_row22_traceSegment_092_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_092 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 288 72 72, g32p_row22_traceSegment_092_0288_0072, g32p_row22_traceSegment_092_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 432 9 9, g32p_row22_traceSegment_092_0432_0009, g32p_row22_traceSegment_092_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 450 9 9, g32p_row22_traceSegment_092_0450_0009, g32p_row22_traceSegment_092_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 432 18 18, g32p_row22_traceSegment_092_0432_0018, g32p_row22_traceSegment_092_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 468 9 9, g32p_row22_traceSegment_092_0468_0009, g32p_row22_traceSegment_092_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 486 9 9, g32p_row22_traceSegment_092_0486_0009, g32p_row22_traceSegment_092_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 468 18 18, g32p_row22_traceSegment_092_0468_0018, g32p_row22_traceSegment_092_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 432 36 36, g32p_row22_traceSegment_092_0432_0036, g32p_row22_traceSegment_092_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 504 9 9, g32p_row22_traceSegment_092_0504_0009, g32p_row22_traceSegment_092_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 522 9 9, g32p_row22_traceSegment_092_0522_0009, g32p_row22_traceSegment_092_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 504 18 18, g32p_row22_traceSegment_092_0504_0018, g32p_row22_traceSegment_092_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 540 9 9, g32p_row22_traceSegment_092_0540_0009, g32p_row22_traceSegment_092_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 558 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_092 567 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_092_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_092 558 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 558 9 9, g32p_row22_traceSegment_092_0558_0009, g32p_row22_traceSegment_092_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_092 540 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 540 18 18, g32p_row22_traceSegment_092_0540_0018, g32p_row22_traceSegment_092_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_092 504 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 504 36 36, g32p_row22_traceSegment_092_0504_0036, g32p_row22_traceSegment_092_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_092 432 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 432 72 72, g32p_row22_traceSegment_092_0432_0072, g32p_row22_traceSegment_092_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_092 288 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 288 144 144, g32p_row22_traceSegment_092_0288_0144, g32p_row22_traceSegment_092_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_092_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_092 0 576 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_092 0 288 288, g32p_row22_traceSegment_092_0000_0288, g32p_row22_traceSegment_092_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 92 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_092_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_094 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 94 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_094_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 0 9 9, g32p_row22_traceSegment_094_0000_0009, g32p_row22_traceSegment_094_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 18 9 9, g32p_row22_traceSegment_094_0018_0009, g32p_row22_traceSegment_094_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 0 18 18, g32p_row22_traceSegment_094_0000_0018, g32p_row22_traceSegment_094_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 36 9 9, g32p_row22_traceSegment_094_0036_0009, g32p_row22_traceSegment_094_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 54 9 9, g32p_row22_traceSegment_094_0054_0009, g32p_row22_traceSegment_094_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 36 18 18, g32p_row22_traceSegment_094_0036_0018, g32p_row22_traceSegment_094_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 0 36 36, g32p_row22_traceSegment_094_0000_0036, g32p_row22_traceSegment_094_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 72 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 72 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 72 9 9, g32p_row22_traceSegment_094_0072_0009, g32p_row22_traceSegment_094_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 90 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 90 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 90 9 9, g32p_row22_traceSegment_094_0090_0009, g32p_row22_traceSegment_094_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 72 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 72 18 18, g32p_row22_traceSegment_094_0072_0018, g32p_row22_traceSegment_094_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 108 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 108 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 108 9 9, g32p_row22_traceSegment_094_0108_0009, g32p_row22_traceSegment_094_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 126 9 9, g32p_row22_traceSegment_094_0126_0009, g32p_row22_traceSegment_094_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 108 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 108 18 18, g32p_row22_traceSegment_094_0108_0018, g32p_row22_traceSegment_094_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 72 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 72 36 36, g32p_row22_traceSegment_094_0072_0036, g32p_row22_traceSegment_094_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_094 0 144 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 0 72 72, g32p_row22_traceSegment_094_0000_0072, g32p_row22_traceSegment_094_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 144 9 9, g32p_row22_traceSegment_094_0144_0009, g32p_row22_traceSegment_094_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 162 9 9, g32p_row22_traceSegment_094_0162_0009, g32p_row22_traceSegment_094_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 144 18 18, g32p_row22_traceSegment_094_0144_0018, g32p_row22_traceSegment_094_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 180 9 9, g32p_row22_traceSegment_094_0180_0009, g32p_row22_traceSegment_094_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 198 9 9, g32p_row22_traceSegment_094_0198_0009, g32p_row22_traceSegment_094_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 180 18 18, g32p_row22_traceSegment_094_0180_0018, g32p_row22_traceSegment_094_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 144 36 36, g32p_row22_traceSegment_094_0144_0036, g32p_row22_traceSegment_094_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 216 9 9, g32p_row22_traceSegment_094_0216_0009, g32p_row22_traceSegment_094_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 234 9 9, g32p_row22_traceSegment_094_0234_0009, g32p_row22_traceSegment_094_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 216 18 18, g32p_row22_traceSegment_094_0216_0018, g32p_row22_traceSegment_094_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 252 9 9, g32p_row22_traceSegment_094_0252_0009, g32p_row22_traceSegment_094_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 270 9 9, g32p_row22_traceSegment_094_0270_0009, g32p_row22_traceSegment_094_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 252 18 18, g32p_row22_traceSegment_094_0252_0018, g32p_row22_traceSegment_094_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 216 36 36, g32p_row22_traceSegment_094_0216_0036, g32p_row22_traceSegment_094_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_094 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 144 72 72, g32p_row22_traceSegment_094_0144_0072, g32p_row22_traceSegment_094_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_094 0 288 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 0 144 144, g32p_row22_traceSegment_094_0000_0144, g32p_row22_traceSegment_094_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 288 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 297 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 288 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 288 9 9, g32p_row22_traceSegment_094_0288_0009, g32p_row22_traceSegment_094_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 315 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 306 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 306 9 9, g32p_row22_traceSegment_094_0306_0009, g32p_row22_traceSegment_094_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 288 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 288 18 18, g32p_row22_traceSegment_094_0288_0018, g32p_row22_traceSegment_094_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 324 9 9, g32p_row22_traceSegment_094_0324_0009, g32p_row22_traceSegment_094_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 342 9 9, g32p_row22_traceSegment_094_0342_0009, g32p_row22_traceSegment_094_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 324 18 18, g32p_row22_traceSegment_094_0324_0018, g32p_row22_traceSegment_094_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 288 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 288 36 36, g32p_row22_traceSegment_094_0288_0036, g32p_row22_traceSegment_094_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 360 9 9, g32p_row22_traceSegment_094_0360_0009, g32p_row22_traceSegment_094_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 378 9 9, g32p_row22_traceSegment_094_0378_0009, g32p_row22_traceSegment_094_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 360 18 18, g32p_row22_traceSegment_094_0360_0018, g32p_row22_traceSegment_094_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 396 9 9, g32p_row22_traceSegment_094_0396_0009, g32p_row22_traceSegment_094_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 414 9 9, g32p_row22_traceSegment_094_0414_0009, g32p_row22_traceSegment_094_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 396 18 18, g32p_row22_traceSegment_094_0396_0018, g32p_row22_traceSegment_094_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 360 36 36, g32p_row22_traceSegment_094_0360_0036, g32p_row22_traceSegment_094_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_094 288 144 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 288 72 72, g32p_row22_traceSegment_094_0288_0072, g32p_row22_traceSegment_094_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 432 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 432 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 432 9 9, g32p_row22_traceSegment_094_0432_0009, g32p_row22_traceSegment_094_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 450 9 9, g32p_row22_traceSegment_094_0450_0009, g32p_row22_traceSegment_094_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 432 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 432 18 18, g32p_row22_traceSegment_094_0432_0018, g32p_row22_traceSegment_094_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 468 9 9, g32p_row22_traceSegment_094_0468_0009, g32p_row22_traceSegment_094_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 495 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 486 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 486 9 9, g32p_row22_traceSegment_094_0486_0009, g32p_row22_traceSegment_094_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 468 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 468 18 18, g32p_row22_traceSegment_094_0468_0018, g32p_row22_traceSegment_094_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 432 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 432 36 36, g32p_row22_traceSegment_094_0432_0036, g32p_row22_traceSegment_094_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 504 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 504 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 504 9 9, g32p_row22_traceSegment_094_0504_0009, g32p_row22_traceSegment_094_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 522 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 522 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 522 9 9, g32p_row22_traceSegment_094_0522_0009, g32p_row22_traceSegment_094_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 504 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 504 18 18, g32p_row22_traceSegment_094_0504_0018, g32p_row22_traceSegment_094_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 540 9 9, g32p_row22_traceSegment_094_0540_0009, g32p_row22_traceSegment_094_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_094 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_094_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_094 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 558 9 9, g32p_row22_traceSegment_094_0558_0009, g32p_row22_traceSegment_094_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_094 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 540 18 18, g32p_row22_traceSegment_094_0540_0018, g32p_row22_traceSegment_094_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_094 504 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 504 36 36, g32p_row22_traceSegment_094_0504_0036, g32p_row22_traceSegment_094_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_094 432 144 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 432 72 72, g32p_row22_traceSegment_094_0432_0072, g32p_row22_traceSegment_094_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_094 288 288 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 288 144 144, g32p_row22_traceSegment_094_0288_0144, g32p_row22_traceSegment_094_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_094_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_094 0 576 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_094 0 288 288, g32p_row22_traceSegment_094_0000_0288, g32p_row22_traceSegment_094_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 94 = [0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_094_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row22_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 69) (g32p_literalTraceValue 21 69)
      [1, -1, 1] [6912, 6912] = true := by
  rw [g32p_row22_traceCoefficients_069]
  decide +kernel

theorem g32p_row22_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 74) (g32p_literalTraceValue 21 74)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_074]
  decide +kernel

theorem g32p_row22_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 78) (g32p_literalTraceValue 21 78)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_078]
  decide +kernel

theorem g32p_row22_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 82) (g32p_literalTraceValue 21 82)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_082]
  decide +kernel

theorem g32p_row22_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 83) (g32p_literalTraceValue 21 83)
      [1, -1, 1] [0, 0, 3456, 3456] = true := by
  rw [g32p_row22_traceCoefficients_083]
  decide +kernel

theorem g32p_row22_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 90) (g32p_literalTraceValue 21 90)
      [1, -1, 1] [-3456] = true := by
  rw [g32p_row22_traceCoefficients_090]
  decide +kernel

theorem g32p_row22_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 92) (g32p_literalTraceValue 21 92)
      [1, -1, 1] [5184, 5184, 5184] = true := by
  rw [g32p_row22_traceCoefficients_092]
  decide +kernel

theorem g32p_row22_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 94) (g32p_literalTraceValue 21 94)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row22_traceCoefficients_094]
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

private def g32p_row22_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_096_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 9 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 0 9 9, g32p_row22_traceSegment_096_0000_0009, g32p_row22_traceSegment_096_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 18 9 9, g32p_row22_traceSegment_096_0018_0009, g32p_row22_traceSegment_096_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 0 18 18, g32p_row22_traceSegment_096_0000_0018, g32p_row22_traceSegment_096_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 36 9 9, g32p_row22_traceSegment_096_0036_0009, g32p_row22_traceSegment_096_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 54 9 9, g32p_row22_traceSegment_096_0054_0009, g32p_row22_traceSegment_096_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 36 18 18, g32p_row22_traceSegment_096_0036_0018, g32p_row22_traceSegment_096_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 0 36 36, g32p_row22_traceSegment_096_0000_0036, g32p_row22_traceSegment_096_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 72 9 9, g32p_row22_traceSegment_096_0072_0009, g32p_row22_traceSegment_096_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 90 9 9, g32p_row22_traceSegment_096_0090_0009, g32p_row22_traceSegment_096_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 72 18 18, g32p_row22_traceSegment_096_0072_0018, g32p_row22_traceSegment_096_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 108 9 9, g32p_row22_traceSegment_096_0108_0009, g32p_row22_traceSegment_096_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 126 9 9, g32p_row22_traceSegment_096_0126_0009, g32p_row22_traceSegment_096_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 108 18 18, g32p_row22_traceSegment_096_0108_0018, g32p_row22_traceSegment_096_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 72 36 36, g32p_row22_traceSegment_096_0072_0036, g32p_row22_traceSegment_096_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_096 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 0 72 72, g32p_row22_traceSegment_096_0000_0072, g32p_row22_traceSegment_096_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 144 9 9, g32p_row22_traceSegment_096_0144_0009, g32p_row22_traceSegment_096_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 162 9 9, g32p_row22_traceSegment_096_0162_0009, g32p_row22_traceSegment_096_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 144 18 18, g32p_row22_traceSegment_096_0144_0018, g32p_row22_traceSegment_096_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 180 9 9, g32p_row22_traceSegment_096_0180_0009, g32p_row22_traceSegment_096_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 198 9 9, g32p_row22_traceSegment_096_0198_0009, g32p_row22_traceSegment_096_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 180 18 18, g32p_row22_traceSegment_096_0180_0018, g32p_row22_traceSegment_096_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 144 36 36, g32p_row22_traceSegment_096_0144_0036, g32p_row22_traceSegment_096_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 216 9 9, g32p_row22_traceSegment_096_0216_0009, g32p_row22_traceSegment_096_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 234 9 9, g32p_row22_traceSegment_096_0234_0009, g32p_row22_traceSegment_096_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 216 18 18, g32p_row22_traceSegment_096_0216_0018, g32p_row22_traceSegment_096_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 252 9 9, g32p_row22_traceSegment_096_0252_0009, g32p_row22_traceSegment_096_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 270 9 9, g32p_row22_traceSegment_096_0270_0009, g32p_row22_traceSegment_096_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 252 18 18, g32p_row22_traceSegment_096_0252_0018, g32p_row22_traceSegment_096_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 216 36 36, g32p_row22_traceSegment_096_0216_0036, g32p_row22_traceSegment_096_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_096 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 144 72 72, g32p_row22_traceSegment_096_0144_0072, g32p_row22_traceSegment_096_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_096 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 0 144 144, g32p_row22_traceSegment_096_0000_0144, g32p_row22_traceSegment_096_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 288 9 9, g32p_row22_traceSegment_096_0288_0009, g32p_row22_traceSegment_096_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 306 9 9, g32p_row22_traceSegment_096_0306_0009, g32p_row22_traceSegment_096_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 288 18 18, g32p_row22_traceSegment_096_0288_0018, g32p_row22_traceSegment_096_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 324 9 9, g32p_row22_traceSegment_096_0324_0009, g32p_row22_traceSegment_096_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 342 9 9, g32p_row22_traceSegment_096_0342_0009, g32p_row22_traceSegment_096_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 324 18 18, g32p_row22_traceSegment_096_0324_0018, g32p_row22_traceSegment_096_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 288 36 36, g32p_row22_traceSegment_096_0288_0036, g32p_row22_traceSegment_096_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 360 9 9, g32p_row22_traceSegment_096_0360_0009, g32p_row22_traceSegment_096_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 378 9 9, g32p_row22_traceSegment_096_0378_0009, g32p_row22_traceSegment_096_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 360 18 18, g32p_row22_traceSegment_096_0360_0018, g32p_row22_traceSegment_096_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 396 9 9, g32p_row22_traceSegment_096_0396_0009, g32p_row22_traceSegment_096_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 414 9 9, g32p_row22_traceSegment_096_0414_0009, g32p_row22_traceSegment_096_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 396 18 18, g32p_row22_traceSegment_096_0396_0018, g32p_row22_traceSegment_096_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 360 36 36, g32p_row22_traceSegment_096_0360_0036, g32p_row22_traceSegment_096_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_096 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 288 72 72, g32p_row22_traceSegment_096_0288_0072, g32p_row22_traceSegment_096_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 432 9 9, g32p_row22_traceSegment_096_0432_0009, g32p_row22_traceSegment_096_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 450 9 9, g32p_row22_traceSegment_096_0450_0009, g32p_row22_traceSegment_096_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 432 18 18, g32p_row22_traceSegment_096_0432_0018, g32p_row22_traceSegment_096_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 468 9 9, g32p_row22_traceSegment_096_0468_0009, g32p_row22_traceSegment_096_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 486 9 9, g32p_row22_traceSegment_096_0486_0009, g32p_row22_traceSegment_096_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 468 18 18, g32p_row22_traceSegment_096_0468_0018, g32p_row22_traceSegment_096_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 432 36 36, g32p_row22_traceSegment_096_0432_0036, g32p_row22_traceSegment_096_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 504 9 9, g32p_row22_traceSegment_096_0504_0009, g32p_row22_traceSegment_096_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 522 9 9, g32p_row22_traceSegment_096_0522_0009, g32p_row22_traceSegment_096_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 504 18 18, g32p_row22_traceSegment_096_0504_0018, g32p_row22_traceSegment_096_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 540 9 9, g32p_row22_traceSegment_096_0540_0009, g32p_row22_traceSegment_096_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_096 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_096_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_096 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 558 9 9, g32p_row22_traceSegment_096_0558_0009, g32p_row22_traceSegment_096_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_096 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 540 18 18, g32p_row22_traceSegment_096_0540_0018, g32p_row22_traceSegment_096_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_096 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 504 36 36, g32p_row22_traceSegment_096_0504_0036, g32p_row22_traceSegment_096_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_096 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 432 72 72, g32p_row22_traceSegment_096_0432_0072, g32p_row22_traceSegment_096_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_096 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 288 144 144, g32p_row22_traceSegment_096_0288_0144, g32p_row22_traceSegment_096_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_096_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_096 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_096 0 288 288, g32p_row22_traceSegment_096_0000_0288, g32p_row22_traceSegment_096_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_096_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_097_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 9 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 0 9 9, g32p_row22_traceSegment_097_0000_0009, g32p_row22_traceSegment_097_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 18 9 9, g32p_row22_traceSegment_097_0018_0009, g32p_row22_traceSegment_097_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 0 18 18, g32p_row22_traceSegment_097_0000_0018, g32p_row22_traceSegment_097_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 36 9 9, g32p_row22_traceSegment_097_0036_0009, g32p_row22_traceSegment_097_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 54 9 9, g32p_row22_traceSegment_097_0054_0009, g32p_row22_traceSegment_097_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 36 18 18, g32p_row22_traceSegment_097_0036_0018, g32p_row22_traceSegment_097_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 0 36 36, g32p_row22_traceSegment_097_0000_0036, g32p_row22_traceSegment_097_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 72 9 9, g32p_row22_traceSegment_097_0072_0009, g32p_row22_traceSegment_097_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 90 9 9, g32p_row22_traceSegment_097_0090_0009, g32p_row22_traceSegment_097_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 72 18 18, g32p_row22_traceSegment_097_0072_0018, g32p_row22_traceSegment_097_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 108 9 9, g32p_row22_traceSegment_097_0108_0009, g32p_row22_traceSegment_097_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 126 9 9, g32p_row22_traceSegment_097_0126_0009, g32p_row22_traceSegment_097_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 108 18 18, g32p_row22_traceSegment_097_0108_0018, g32p_row22_traceSegment_097_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 72 36 36, g32p_row22_traceSegment_097_0072_0036, g32p_row22_traceSegment_097_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_097 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 0 72 72, g32p_row22_traceSegment_097_0000_0072, g32p_row22_traceSegment_097_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 144 9 9, g32p_row22_traceSegment_097_0144_0009, g32p_row22_traceSegment_097_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 162 9 9, g32p_row22_traceSegment_097_0162_0009, g32p_row22_traceSegment_097_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 144 18 18, g32p_row22_traceSegment_097_0144_0018, g32p_row22_traceSegment_097_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 180 9 9, g32p_row22_traceSegment_097_0180_0009, g32p_row22_traceSegment_097_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 198 9 9, g32p_row22_traceSegment_097_0198_0009, g32p_row22_traceSegment_097_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 180 18 18, g32p_row22_traceSegment_097_0180_0018, g32p_row22_traceSegment_097_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 144 36 36, g32p_row22_traceSegment_097_0144_0036, g32p_row22_traceSegment_097_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 216 9 9, g32p_row22_traceSegment_097_0216_0009, g32p_row22_traceSegment_097_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 234 9 9, g32p_row22_traceSegment_097_0234_0009, g32p_row22_traceSegment_097_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 216 18 18, g32p_row22_traceSegment_097_0216_0018, g32p_row22_traceSegment_097_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 252 9 9, g32p_row22_traceSegment_097_0252_0009, g32p_row22_traceSegment_097_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 270 9 9, g32p_row22_traceSegment_097_0270_0009, g32p_row22_traceSegment_097_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 252 18 18, g32p_row22_traceSegment_097_0252_0018, g32p_row22_traceSegment_097_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 216 36 36, g32p_row22_traceSegment_097_0216_0036, g32p_row22_traceSegment_097_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_097 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 144 72 72, g32p_row22_traceSegment_097_0144_0072, g32p_row22_traceSegment_097_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_097 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 0 144 144, g32p_row22_traceSegment_097_0000_0144, g32p_row22_traceSegment_097_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 288 9 9, g32p_row22_traceSegment_097_0288_0009, g32p_row22_traceSegment_097_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 306 9 9, g32p_row22_traceSegment_097_0306_0009, g32p_row22_traceSegment_097_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 288 18 18, g32p_row22_traceSegment_097_0288_0018, g32p_row22_traceSegment_097_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 324 9 9, g32p_row22_traceSegment_097_0324_0009, g32p_row22_traceSegment_097_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 342 9 9, g32p_row22_traceSegment_097_0342_0009, g32p_row22_traceSegment_097_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 324 18 18, g32p_row22_traceSegment_097_0324_0018, g32p_row22_traceSegment_097_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 288 36 36, g32p_row22_traceSegment_097_0288_0036, g32p_row22_traceSegment_097_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 360 9 9, g32p_row22_traceSegment_097_0360_0009, g32p_row22_traceSegment_097_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 378 9 9, g32p_row22_traceSegment_097_0378_0009, g32p_row22_traceSegment_097_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 360 18 18, g32p_row22_traceSegment_097_0360_0018, g32p_row22_traceSegment_097_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 396 9 9, g32p_row22_traceSegment_097_0396_0009, g32p_row22_traceSegment_097_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 414 9 9, g32p_row22_traceSegment_097_0414_0009, g32p_row22_traceSegment_097_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 396 18 18, g32p_row22_traceSegment_097_0396_0018, g32p_row22_traceSegment_097_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 360 36 36, g32p_row22_traceSegment_097_0360_0036, g32p_row22_traceSegment_097_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_097 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 288 72 72, g32p_row22_traceSegment_097_0288_0072, g32p_row22_traceSegment_097_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 432 9 9, g32p_row22_traceSegment_097_0432_0009, g32p_row22_traceSegment_097_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 450 9 9, g32p_row22_traceSegment_097_0450_0009, g32p_row22_traceSegment_097_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 432 18 18, g32p_row22_traceSegment_097_0432_0018, g32p_row22_traceSegment_097_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 468 9 9, g32p_row22_traceSegment_097_0468_0009, g32p_row22_traceSegment_097_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 486 9 9, g32p_row22_traceSegment_097_0486_0009, g32p_row22_traceSegment_097_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 468 18 18, g32p_row22_traceSegment_097_0468_0018, g32p_row22_traceSegment_097_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 432 36 36, g32p_row22_traceSegment_097_0432_0036, g32p_row22_traceSegment_097_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 504 9 9, g32p_row22_traceSegment_097_0504_0009, g32p_row22_traceSegment_097_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 522 9 9, g32p_row22_traceSegment_097_0522_0009, g32p_row22_traceSegment_097_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 504 18 18, g32p_row22_traceSegment_097_0504_0018, g32p_row22_traceSegment_097_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 540 9 9, g32p_row22_traceSegment_097_0540_0009, g32p_row22_traceSegment_097_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_097 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_097_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_097 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 558 9 9, g32p_row22_traceSegment_097_0558_0009, g32p_row22_traceSegment_097_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_097 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 540 18 18, g32p_row22_traceSegment_097_0540_0018, g32p_row22_traceSegment_097_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_097 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 504 36 36, g32p_row22_traceSegment_097_0504_0036, g32p_row22_traceSegment_097_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_097 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 432 72 72, g32p_row22_traceSegment_097_0432_0072, g32p_row22_traceSegment_097_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_097 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 288 144 144, g32p_row22_traceSegment_097_0288_0144, g32p_row22_traceSegment_097_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_097_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_097 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_097 0 288 288, g32p_row22_traceSegment_097_0000_0288, g32p_row22_traceSegment_097_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_097_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_099_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 0 9 9, g32p_row22_traceSegment_099_0000_0009, g32p_row22_traceSegment_099_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 18 9 9, g32p_row22_traceSegment_099_0018_0009, g32p_row22_traceSegment_099_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 0 18 18, g32p_row22_traceSegment_099_0000_0018, g32p_row22_traceSegment_099_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 36 9 9, g32p_row22_traceSegment_099_0036_0009, g32p_row22_traceSegment_099_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 54 9 9, g32p_row22_traceSegment_099_0054_0009, g32p_row22_traceSegment_099_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 36 18 18, g32p_row22_traceSegment_099_0036_0018, g32p_row22_traceSegment_099_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 0 36 36, g32p_row22_traceSegment_099_0000_0036, g32p_row22_traceSegment_099_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 72 9 9, g32p_row22_traceSegment_099_0072_0009, g32p_row22_traceSegment_099_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 99 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 90 9 9, g32p_row22_traceSegment_099_0090_0009, g32p_row22_traceSegment_099_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 72 18 18, g32p_row22_traceSegment_099_0072_0018, g32p_row22_traceSegment_099_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 108 9 9, g32p_row22_traceSegment_099_0108_0009, g32p_row22_traceSegment_099_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 126 9 9, g32p_row22_traceSegment_099_0126_0009, g32p_row22_traceSegment_099_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 108 18 18, g32p_row22_traceSegment_099_0108_0018, g32p_row22_traceSegment_099_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 72 36 36, g32p_row22_traceSegment_099_0072_0036, g32p_row22_traceSegment_099_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_099 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 0 72 72, g32p_row22_traceSegment_099_0000_0072, g32p_row22_traceSegment_099_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 144 9 9, g32p_row22_traceSegment_099_0144_0009, g32p_row22_traceSegment_099_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 162 9 9, g32p_row22_traceSegment_099_0162_0009, g32p_row22_traceSegment_099_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 144 18 18, g32p_row22_traceSegment_099_0144_0018, g32p_row22_traceSegment_099_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 180 9 9, g32p_row22_traceSegment_099_0180_0009, g32p_row22_traceSegment_099_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 198 9 9, g32p_row22_traceSegment_099_0198_0009, g32p_row22_traceSegment_099_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 180 18 18, g32p_row22_traceSegment_099_0180_0018, g32p_row22_traceSegment_099_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 144 36 36, g32p_row22_traceSegment_099_0144_0036, g32p_row22_traceSegment_099_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 216 9 9, g32p_row22_traceSegment_099_0216_0009, g32p_row22_traceSegment_099_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 234 9 9, g32p_row22_traceSegment_099_0234_0009, g32p_row22_traceSegment_099_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 216 18 18, g32p_row22_traceSegment_099_0216_0018, g32p_row22_traceSegment_099_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 252 9 9, g32p_row22_traceSegment_099_0252_0009, g32p_row22_traceSegment_099_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 270 9 9, g32p_row22_traceSegment_099_0270_0009, g32p_row22_traceSegment_099_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 252 18 18, g32p_row22_traceSegment_099_0252_0018, g32p_row22_traceSegment_099_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 216 36 36, g32p_row22_traceSegment_099_0216_0036, g32p_row22_traceSegment_099_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_099 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 144 72 72, g32p_row22_traceSegment_099_0144_0072, g32p_row22_traceSegment_099_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_099 0 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 0 144 144, g32p_row22_traceSegment_099_0000_0144, g32p_row22_traceSegment_099_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 288 9 = [1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 288 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 288 9 9, g32p_row22_traceSegment_099_0288_0009, g32p_row22_traceSegment_099_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 306 9 9, g32p_row22_traceSegment_099_0306_0009, g32p_row22_traceSegment_099_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 288 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 288 18 18, g32p_row22_traceSegment_099_0288_0018, g32p_row22_traceSegment_099_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 324 9 9, g32p_row22_traceSegment_099_0324_0009, g32p_row22_traceSegment_099_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 342 9 9, g32p_row22_traceSegment_099_0342_0009, g32p_row22_traceSegment_099_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 324 18 18, g32p_row22_traceSegment_099_0324_0018, g32p_row22_traceSegment_099_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 288 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 288 36 36, g32p_row22_traceSegment_099_0288_0036, g32p_row22_traceSegment_099_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 360 9 9, g32p_row22_traceSegment_099_0360_0009, g32p_row22_traceSegment_099_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 378 9 9, g32p_row22_traceSegment_099_0378_0009, g32p_row22_traceSegment_099_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 360 18 18, g32p_row22_traceSegment_099_0360_0018, g32p_row22_traceSegment_099_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 396 9 9, g32p_row22_traceSegment_099_0396_0009, g32p_row22_traceSegment_099_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 414 9 9, g32p_row22_traceSegment_099_0414_0009, g32p_row22_traceSegment_099_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 396 18 18, g32p_row22_traceSegment_099_0396_0018, g32p_row22_traceSegment_099_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 360 36 36, g32p_row22_traceSegment_099_0360_0036, g32p_row22_traceSegment_099_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_099 288 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 288 72 72, g32p_row22_traceSegment_099_0288_0072, g32p_row22_traceSegment_099_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 432 9 9, g32p_row22_traceSegment_099_0432_0009, g32p_row22_traceSegment_099_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 450 9 9, g32p_row22_traceSegment_099_0450_0009, g32p_row22_traceSegment_099_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 432 18 18, g32p_row22_traceSegment_099_0432_0018, g32p_row22_traceSegment_099_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 468 9 9, g32p_row22_traceSegment_099_0468_0009, g32p_row22_traceSegment_099_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 486 9 9, g32p_row22_traceSegment_099_0486_0009, g32p_row22_traceSegment_099_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 468 18 18, g32p_row22_traceSegment_099_0468_0018, g32p_row22_traceSegment_099_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 432 36 36, g32p_row22_traceSegment_099_0432_0036, g32p_row22_traceSegment_099_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 504 9 9, g32p_row22_traceSegment_099_0504_0009, g32p_row22_traceSegment_099_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 522 9 9, g32p_row22_traceSegment_099_0522_0009, g32p_row22_traceSegment_099_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 504 18 18, g32p_row22_traceSegment_099_0504_0018, g32p_row22_traceSegment_099_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 540 9 9, g32p_row22_traceSegment_099_0540_0009, g32p_row22_traceSegment_099_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_099 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_099_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_099 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 558 9 9, g32p_row22_traceSegment_099_0558_0009, g32p_row22_traceSegment_099_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_099 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 540 18 18, g32p_row22_traceSegment_099_0540_0018, g32p_row22_traceSegment_099_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_099 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 504 36 36, g32p_row22_traceSegment_099_0504_0036, g32p_row22_traceSegment_099_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_099 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 432 72 72, g32p_row22_traceSegment_099_0432_0072, g32p_row22_traceSegment_099_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_099 288 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 288 144 144, g32p_row22_traceSegment_099_0288_0144, g32p_row22_traceSegment_099_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_099_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_099 0 576 = [1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_099 0 288 288, g32p_row22_traceSegment_099_0000_0288, g32p_row22_traceSegment_099_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_099_0000_0576

end HodgeLean.Foundations.Program

end
end
