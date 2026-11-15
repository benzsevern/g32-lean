import HodgeLean.Foundations.Program.G32PropFourSixPacked0376
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0378

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_065_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 0 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 9 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 0 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 9 9, g32p_row19_traceSegment_065_0000_0009, g32p_row19_traceSegment_065_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 18 9 9, g32p_row19_traceSegment_065_0018_0009, g32p_row19_traceSegment_065_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 0 36 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 18 18, g32p_row19_traceSegment_065_0000_0018, g32p_row19_traceSegment_065_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 36 9 9, g32p_row19_traceSegment_065_0036_0009, g32p_row19_traceSegment_065_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 54 9 9, g32p_row19_traceSegment_065_0054_0009, g32p_row19_traceSegment_065_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 36 18 18, g32p_row19_traceSegment_065_0036_0018, g32p_row19_traceSegment_065_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 0 72 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 36 36, g32p_row19_traceSegment_065_0000_0036, g32p_row19_traceSegment_065_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 72 9 9, g32p_row19_traceSegment_065_0072_0009, g32p_row19_traceSegment_065_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 90 9 9, g32p_row19_traceSegment_065_0090_0009, g32p_row19_traceSegment_065_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 72 18 18, g32p_row19_traceSegment_065_0072_0018, g32p_row19_traceSegment_065_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 108 9 9, g32p_row19_traceSegment_065_0108_0009, g32p_row19_traceSegment_065_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 126 9 9, g32p_row19_traceSegment_065_0126_0009, g32p_row19_traceSegment_065_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 108 18 18, g32p_row19_traceSegment_065_0108_0018, g32p_row19_traceSegment_065_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 72 36 36, g32p_row19_traceSegment_065_0072_0036, g32p_row19_traceSegment_065_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 0 144 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 72 72, g32p_row19_traceSegment_065_0000_0072, g32p_row19_traceSegment_065_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 144 9 9, g32p_row19_traceSegment_065_0144_0009, g32p_row19_traceSegment_065_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 162 9 9, g32p_row19_traceSegment_065_0162_0009, g32p_row19_traceSegment_065_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 144 18 18, g32p_row19_traceSegment_065_0144_0018, g32p_row19_traceSegment_065_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 180 9 9, g32p_row19_traceSegment_065_0180_0009, g32p_row19_traceSegment_065_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 198 9 9, g32p_row19_traceSegment_065_0198_0009, g32p_row19_traceSegment_065_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 180 18 18, g32p_row19_traceSegment_065_0180_0018, g32p_row19_traceSegment_065_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 144 36 36, g32p_row19_traceSegment_065_0144_0036, g32p_row19_traceSegment_065_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 216 9 9, g32p_row19_traceSegment_065_0216_0009, g32p_row19_traceSegment_065_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 234 9 9, g32p_row19_traceSegment_065_0234_0009, g32p_row19_traceSegment_065_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 216 18 18, g32p_row19_traceSegment_065_0216_0018, g32p_row19_traceSegment_065_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 252 9 9, g32p_row19_traceSegment_065_0252_0009, g32p_row19_traceSegment_065_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 270 9 9, g32p_row19_traceSegment_065_0270_0009, g32p_row19_traceSegment_065_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 252 18 18, g32p_row19_traceSegment_065_0252_0018, g32p_row19_traceSegment_065_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 216 36 36, g32p_row19_traceSegment_065_0216_0036, g32p_row19_traceSegment_065_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 144 72 72, g32p_row19_traceSegment_065_0144_0072, g32p_row19_traceSegment_065_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_065 0 288 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 144 144, g32p_row19_traceSegment_065_0000_0144, g32p_row19_traceSegment_065_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 288 9 9, g32p_row19_traceSegment_065_0288_0009, g32p_row19_traceSegment_065_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 306 9 9, g32p_row19_traceSegment_065_0306_0009, g32p_row19_traceSegment_065_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 288 18 18, g32p_row19_traceSegment_065_0288_0018, g32p_row19_traceSegment_065_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 324 9 9, g32p_row19_traceSegment_065_0324_0009, g32p_row19_traceSegment_065_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 342 9 9, g32p_row19_traceSegment_065_0342_0009, g32p_row19_traceSegment_065_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 324 18 18, g32p_row19_traceSegment_065_0324_0018, g32p_row19_traceSegment_065_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 288 36 36, g32p_row19_traceSegment_065_0288_0036, g32p_row19_traceSegment_065_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 360 9 9, g32p_row19_traceSegment_065_0360_0009, g32p_row19_traceSegment_065_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 378 9 9, g32p_row19_traceSegment_065_0378_0009, g32p_row19_traceSegment_065_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 360 18 18, g32p_row19_traceSegment_065_0360_0018, g32p_row19_traceSegment_065_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 396 9 9, g32p_row19_traceSegment_065_0396_0009, g32p_row19_traceSegment_065_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 414 9 9, g32p_row19_traceSegment_065_0414_0009, g32p_row19_traceSegment_065_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 396 18 18, g32p_row19_traceSegment_065_0396_0018, g32p_row19_traceSegment_065_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 360 36 36, g32p_row19_traceSegment_065_0360_0036, g32p_row19_traceSegment_065_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 288 72 72, g32p_row19_traceSegment_065_0288_0072, g32p_row19_traceSegment_065_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 432 9 9, g32p_row19_traceSegment_065_0432_0009, g32p_row19_traceSegment_065_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 450 9 9, g32p_row19_traceSegment_065_0450_0009, g32p_row19_traceSegment_065_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 432 18 18, g32p_row19_traceSegment_065_0432_0018, g32p_row19_traceSegment_065_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 468 9 9, g32p_row19_traceSegment_065_0468_0009, g32p_row19_traceSegment_065_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 486 9 9, g32p_row19_traceSegment_065_0486_0009, g32p_row19_traceSegment_065_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 468 18 18, g32p_row19_traceSegment_065_0468_0018, g32p_row19_traceSegment_065_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 432 36 36, g32p_row19_traceSegment_065_0432_0036, g32p_row19_traceSegment_065_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 504 9 9, g32p_row19_traceSegment_065_0504_0009, g32p_row19_traceSegment_065_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 522 9 9, g32p_row19_traceSegment_065_0522_0009, g32p_row19_traceSegment_065_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 504 18 18, g32p_row19_traceSegment_065_0504_0018, g32p_row19_traceSegment_065_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 540 9 9, g32p_row19_traceSegment_065_0540_0009, g32p_row19_traceSegment_065_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 558 9 9, g32p_row19_traceSegment_065_0558_0009, g32p_row19_traceSegment_065_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 540 18 18, g32p_row19_traceSegment_065_0540_0018, g32p_row19_traceSegment_065_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 504 36 36, g32p_row19_traceSegment_065_0504_0036, g32p_row19_traceSegment_065_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 432 72 72, g32p_row19_traceSegment_065_0432_0072, g32p_row19_traceSegment_065_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_065 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 288 144 144, g32p_row19_traceSegment_065_0288_0144, g32p_row19_traceSegment_065_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_065 0 576 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 288 288, g32p_row19_traceSegment_065_0000_0288, g32p_row19_traceSegment_065_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 576 9 9, g32p_row19_traceSegment_065_0576_0009, g32p_row19_traceSegment_065_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 594 9 9, g32p_row19_traceSegment_065_0594_0009, g32p_row19_traceSegment_065_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 576 18 18, g32p_row19_traceSegment_065_0576_0018, g32p_row19_traceSegment_065_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 612 9 9, g32p_row19_traceSegment_065_0612_0009, g32p_row19_traceSegment_065_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 630 9 9, g32p_row19_traceSegment_065_0630_0009, g32p_row19_traceSegment_065_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 612 18 18, g32p_row19_traceSegment_065_0612_0018, g32p_row19_traceSegment_065_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 576 36 36, g32p_row19_traceSegment_065_0576_0036, g32p_row19_traceSegment_065_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 648 9 9, g32p_row19_traceSegment_065_0648_0009, g32p_row19_traceSegment_065_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 666 9 9, g32p_row19_traceSegment_065_0666_0009, g32p_row19_traceSegment_065_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 648 18 18, g32p_row19_traceSegment_065_0648_0018, g32p_row19_traceSegment_065_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 684 9 9, g32p_row19_traceSegment_065_0684_0009, g32p_row19_traceSegment_065_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 702 9 9, g32p_row19_traceSegment_065_0702_0009, g32p_row19_traceSegment_065_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 684 18 18, g32p_row19_traceSegment_065_0684_0018, g32p_row19_traceSegment_065_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 648 36 36, g32p_row19_traceSegment_065_0648_0036, g32p_row19_traceSegment_065_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 576 72 72, g32p_row19_traceSegment_065_0576_0072, g32p_row19_traceSegment_065_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 720 9 9, g32p_row19_traceSegment_065_0720_0009, g32p_row19_traceSegment_065_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 738 9 9, g32p_row19_traceSegment_065_0738_0009, g32p_row19_traceSegment_065_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 720 18 18, g32p_row19_traceSegment_065_0720_0018, g32p_row19_traceSegment_065_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 756 9 9, g32p_row19_traceSegment_065_0756_0009, g32p_row19_traceSegment_065_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 774 9 9, g32p_row19_traceSegment_065_0774_0009, g32p_row19_traceSegment_065_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 756 18 18, g32p_row19_traceSegment_065_0756_0018, g32p_row19_traceSegment_065_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 720 36 36, g32p_row19_traceSegment_065_0720_0036, g32p_row19_traceSegment_065_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 792 9 9, g32p_row19_traceSegment_065_0792_0009, g32p_row19_traceSegment_065_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 810 9 9, g32p_row19_traceSegment_065_0810_0009, g32p_row19_traceSegment_065_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 792 18 18, g32p_row19_traceSegment_065_0792_0018, g32p_row19_traceSegment_065_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 828 9 9, g32p_row19_traceSegment_065_0828_0009, g32p_row19_traceSegment_065_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 846 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 846 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 846 9 9, g32p_row19_traceSegment_065_0846_0009, g32p_row19_traceSegment_065_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 828 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 828 18 18, g32p_row19_traceSegment_065_0828_0018, g32p_row19_traceSegment_065_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 792 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 792 36 36, g32p_row19_traceSegment_065_0792_0036, g32p_row19_traceSegment_065_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 720 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 720 72 72, g32p_row19_traceSegment_065_0720_0072, g32p_row19_traceSegment_065_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_065 576 288 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 576 144 144, g32p_row19_traceSegment_065_0576_0144, g32p_row19_traceSegment_065_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 864 9 9, g32p_row19_traceSegment_065_0864_0009, g32p_row19_traceSegment_065_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 891 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 882 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 882 9 9, g32p_row19_traceSegment_065_0882_0009, g32p_row19_traceSegment_065_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 864 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 864 18 18, g32p_row19_traceSegment_065_0864_0018, g32p_row19_traceSegment_065_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 900 9 9, g32p_row19_traceSegment_065_0900_0009, g32p_row19_traceSegment_065_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 918 9 9, g32p_row19_traceSegment_065_0918_0009, g32p_row19_traceSegment_065_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 900 18 18, g32p_row19_traceSegment_065_0900_0018, g32p_row19_traceSegment_065_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 864 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 864 36 36, g32p_row19_traceSegment_065_0864_0036, g32p_row19_traceSegment_065_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 936 9 9, g32p_row19_traceSegment_065_0936_0009, g32p_row19_traceSegment_065_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 954 9 9, g32p_row19_traceSegment_065_0954_0009, g32p_row19_traceSegment_065_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 936 18 18, g32p_row19_traceSegment_065_0936_0018, g32p_row19_traceSegment_065_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 972 9 9, g32p_row19_traceSegment_065_0972_0009, g32p_row19_traceSegment_065_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 990 9 9, g32p_row19_traceSegment_065_0990_0009, g32p_row19_traceSegment_065_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 972 18 18, g32p_row19_traceSegment_065_0972_0018, g32p_row19_traceSegment_065_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 936 36 36, g32p_row19_traceSegment_065_0936_0036, g32p_row19_traceSegment_065_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 864 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 864 72 72, g32p_row19_traceSegment_065_0864_0072, g32p_row19_traceSegment_065_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1008 9 9, g32p_row19_traceSegment_065_1008_0009, g32p_row19_traceSegment_065_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1026 9 9, g32p_row19_traceSegment_065_1026_0009, g32p_row19_traceSegment_065_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1008 18 18, g32p_row19_traceSegment_065_1008_0018, g32p_row19_traceSegment_065_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1044 9 9, g32p_row19_traceSegment_065_1044_0009, g32p_row19_traceSegment_065_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1062 9 9, g32p_row19_traceSegment_065_1062_0009, g32p_row19_traceSegment_065_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1044 18 18, g32p_row19_traceSegment_065_1044_0018, g32p_row19_traceSegment_065_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1008 36 36, g32p_row19_traceSegment_065_1008_0036, g32p_row19_traceSegment_065_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1080 9 9, g32p_row19_traceSegment_065_1080_0009, g32p_row19_traceSegment_065_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1098 9 9, g32p_row19_traceSegment_065_1098_0009, g32p_row19_traceSegment_065_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1080 18 18, g32p_row19_traceSegment_065_1080_0018, g32p_row19_traceSegment_065_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1125 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1116 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1116 9 9, g32p_row19_traceSegment_065_1116_0009, g32p_row19_traceSegment_065_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_065 1143 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_065_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_065 1134 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1134 9 9, g32p_row19_traceSegment_065_1134_0009, g32p_row19_traceSegment_065_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_065 1116 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1116 18 18, g32p_row19_traceSegment_065_1116_0018, g32p_row19_traceSegment_065_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_065 1080 72 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1080 36 36, g32p_row19_traceSegment_065_1080_0036, g32p_row19_traceSegment_065_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_065_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_065 1008 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 1008 72 72, g32p_row19_traceSegment_065_1008_0072, g32p_row19_traceSegment_065_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_065 864 288 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 864 144 144, g32p_row19_traceSegment_065_0864_0144, g32p_row19_traceSegment_065_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_065 576 576 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 576 288 288, g32p_row19_traceSegment_065_0576_0288, g32p_row19_traceSegment_065_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_065_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_065 0 1152 = [0, 8, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_065 0 576 576, g32p_row19_traceSegment_065_0000_0576, g32p_row19_traceSegment_065_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 65 = [0, 8, 0, 0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_065_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row19_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 46) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 46) (g32p_literalTraceValue 18 46)
      [1, -1, 1] [0, 1152] = true := by
  rw [g32p_row19_traceCoefficients_046]
  decide +kernel

theorem g32p_row19_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 49) (g32p_literalTraceValue 18 49)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row19_traceCoefficients_049]
  decide +kernel

theorem g32p_row19_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 50) (g32p_literalTraceValue 18 50)
      [1, -1, 1] [6912, 6912, 3456] = true := by
  rw [g32p_row19_traceCoefficients_050]
  decide +kernel

theorem g32p_row19_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 52) (g32p_literalTraceValue 18 52)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_052]
  decide +kernel

theorem g32p_row19_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 56) (g32p_literalTraceValue 18 56)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row19_traceCoefficients_056]
  decide +kernel

theorem g32p_row19_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 57) (g32p_literalTraceValue 18 57)
      [1, -1, 1] [-1152] = true := by
  rw [g32p_row19_traceCoefficients_057]
  decide +kernel

theorem g32p_row19_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 59) (g32p_literalTraceValue 18 59)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row19_traceCoefficients_059]
  decide +kernel

theorem g32p_row19_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 65) (g32p_literalTraceValue 18 65)
      [1, -1, 1] [-10368, 3456, 3456] = true := by
  rw [g32p_row19_traceCoefficients_065]
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

private def g32p_row19_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_069_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 9 9, g32p_row19_traceSegment_069_0000_0009, g32p_row19_traceSegment_069_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 18 9 9, g32p_row19_traceSegment_069_0018_0009, g32p_row19_traceSegment_069_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 18 18, g32p_row19_traceSegment_069_0000_0018, g32p_row19_traceSegment_069_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 45 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 36 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 36 9 9, g32p_row19_traceSegment_069_0036_0009, g32p_row19_traceSegment_069_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 54 9 9, g32p_row19_traceSegment_069_0054_0009, g32p_row19_traceSegment_069_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 36 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 36 18 18, g32p_row19_traceSegment_069_0036_0018, g32p_row19_traceSegment_069_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 36 36, g32p_row19_traceSegment_069_0000_0036, g32p_row19_traceSegment_069_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 72 9 9, g32p_row19_traceSegment_069_0072_0009, g32p_row19_traceSegment_069_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 90 9 9, g32p_row19_traceSegment_069_0090_0009, g32p_row19_traceSegment_069_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 72 18 18, g32p_row19_traceSegment_069_0072_0018, g32p_row19_traceSegment_069_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 117 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 108 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 108 9 9, g32p_row19_traceSegment_069_0108_0009, g32p_row19_traceSegment_069_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 126 9 9, g32p_row19_traceSegment_069_0126_0009, g32p_row19_traceSegment_069_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 108 18 18, g32p_row19_traceSegment_069_0108_0018, g32p_row19_traceSegment_069_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 72 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 72 36 36, g32p_row19_traceSegment_069_0072_0036, g32p_row19_traceSegment_069_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 72 72, g32p_row19_traceSegment_069_0000_0072, g32p_row19_traceSegment_069_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 144 9 9, g32p_row19_traceSegment_069_0144_0009, g32p_row19_traceSegment_069_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 162 9 9, g32p_row19_traceSegment_069_0162_0009, g32p_row19_traceSegment_069_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 144 18 18, g32p_row19_traceSegment_069_0144_0018, g32p_row19_traceSegment_069_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 180 9 9, g32p_row19_traceSegment_069_0180_0009, g32p_row19_traceSegment_069_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 198 9 9, g32p_row19_traceSegment_069_0198_0009, g32p_row19_traceSegment_069_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 180 18 18, g32p_row19_traceSegment_069_0180_0018, g32p_row19_traceSegment_069_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 144 36 36, g32p_row19_traceSegment_069_0144_0036, g32p_row19_traceSegment_069_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 216 9 9, g32p_row19_traceSegment_069_0216_0009, g32p_row19_traceSegment_069_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 234 9 9, g32p_row19_traceSegment_069_0234_0009, g32p_row19_traceSegment_069_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 216 18 18, g32p_row19_traceSegment_069_0216_0018, g32p_row19_traceSegment_069_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 252 9 9, g32p_row19_traceSegment_069_0252_0009, g32p_row19_traceSegment_069_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 270 9 9, g32p_row19_traceSegment_069_0270_0009, g32p_row19_traceSegment_069_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 252 18 18, g32p_row19_traceSegment_069_0252_0018, g32p_row19_traceSegment_069_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 216 36 36, g32p_row19_traceSegment_069_0216_0036, g32p_row19_traceSegment_069_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 144 72 72, g32p_row19_traceSegment_069_0144_0072, g32p_row19_traceSegment_069_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_069 0 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 144 144, g32p_row19_traceSegment_069_0000_0144, g32p_row19_traceSegment_069_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 288 9 9, g32p_row19_traceSegment_069_0288_0009, g32p_row19_traceSegment_069_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 306 9 9, g32p_row19_traceSegment_069_0306_0009, g32p_row19_traceSegment_069_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 288 18 18, g32p_row19_traceSegment_069_0288_0018, g32p_row19_traceSegment_069_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 324 9 9, g32p_row19_traceSegment_069_0324_0009, g32p_row19_traceSegment_069_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 342 9 9, g32p_row19_traceSegment_069_0342_0009, g32p_row19_traceSegment_069_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 324 18 18, g32p_row19_traceSegment_069_0324_0018, g32p_row19_traceSegment_069_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 288 36 36, g32p_row19_traceSegment_069_0288_0036, g32p_row19_traceSegment_069_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 369 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 360 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 360 9 9, g32p_row19_traceSegment_069_0360_0009, g32p_row19_traceSegment_069_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 378 9 9, g32p_row19_traceSegment_069_0378_0009, g32p_row19_traceSegment_069_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 360 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 360 18 18, g32p_row19_traceSegment_069_0360_0018, g32p_row19_traceSegment_069_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 396 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 396 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 396 9 9, g32p_row19_traceSegment_069_0396_0009, g32p_row19_traceSegment_069_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 414 9 9, g32p_row19_traceSegment_069_0414_0009, g32p_row19_traceSegment_069_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 396 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 396 18 18, g32p_row19_traceSegment_069_0396_0018, g32p_row19_traceSegment_069_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 360 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 360 36 36, g32p_row19_traceSegment_069_0360_0036, g32p_row19_traceSegment_069_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 288 144 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 288 72 72, g32p_row19_traceSegment_069_0288_0072, g32p_row19_traceSegment_069_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 432 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 441 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 432 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 432 9 9, g32p_row19_traceSegment_069_0432_0009, g32p_row19_traceSegment_069_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 450 9 9, g32p_row19_traceSegment_069_0450_0009, g32p_row19_traceSegment_069_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 432 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 432 18 18, g32p_row19_traceSegment_069_0432_0018, g32p_row19_traceSegment_069_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 468 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 468 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 468 9 9, g32p_row19_traceSegment_069_0468_0009, g32p_row19_traceSegment_069_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 495 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 486 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 486 9 9, g32p_row19_traceSegment_069_0486_0009, g32p_row19_traceSegment_069_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 468 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 468 18 18, g32p_row19_traceSegment_069_0468_0018, g32p_row19_traceSegment_069_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 432 72 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 432 36 36, g32p_row19_traceSegment_069_0432_0036, g32p_row19_traceSegment_069_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 504 9 9, g32p_row19_traceSegment_069_0504_0009, g32p_row19_traceSegment_069_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 531 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 522 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 522 9 9, g32p_row19_traceSegment_069_0522_0009, g32p_row19_traceSegment_069_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 504 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 504 18 18, g32p_row19_traceSegment_069_0504_0018, g32p_row19_traceSegment_069_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 540 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 540 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 540 9 9, g32p_row19_traceSegment_069_0540_0009, g32p_row19_traceSegment_069_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 558 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 558 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 558 9 9, g32p_row19_traceSegment_069_0558_0009, g32p_row19_traceSegment_069_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 540 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 540 18 18, g32p_row19_traceSegment_069_0540_0018, g32p_row19_traceSegment_069_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 504 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 504 36 36, g32p_row19_traceSegment_069_0504_0036, g32p_row19_traceSegment_069_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 432 144 = [8, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 432 72 72, g32p_row19_traceSegment_069_0432_0072, g32p_row19_traceSegment_069_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_069 288 288 = [8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 288 144 144, g32p_row19_traceSegment_069_0288_0144, g32p_row19_traceSegment_069_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_069 0 576 = [10, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 288 288, g32p_row19_traceSegment_069_0000_0288, g32p_row19_traceSegment_069_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 576 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 576 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 576 9 9, g32p_row19_traceSegment_069_0576_0009, g32p_row19_traceSegment_069_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 594 9 9, g32p_row19_traceSegment_069_0594_0009, g32p_row19_traceSegment_069_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 576 18 18, g32p_row19_traceSegment_069_0576_0018, g32p_row19_traceSegment_069_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 612 9 9, g32p_row19_traceSegment_069_0612_0009, g32p_row19_traceSegment_069_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 630 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 630 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 630 9 9, g32p_row19_traceSegment_069_0630_0009, g32p_row19_traceSegment_069_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 612 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 612 18 18, g32p_row19_traceSegment_069_0612_0018, g32p_row19_traceSegment_069_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 576 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 576 36 36, g32p_row19_traceSegment_069_0576_0036, g32p_row19_traceSegment_069_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 648 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 648 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 648 9 9, g32p_row19_traceSegment_069_0648_0009, g32p_row19_traceSegment_069_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 666 9 9, g32p_row19_traceSegment_069_0666_0009, g32p_row19_traceSegment_069_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 648 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 648 18 18, g32p_row19_traceSegment_069_0648_0018, g32p_row19_traceSegment_069_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 693 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 684 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 684 9 9, g32p_row19_traceSegment_069_0684_0009, g32p_row19_traceSegment_069_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 702 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 702 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 702 9 9, g32p_row19_traceSegment_069_0702_0009, g32p_row19_traceSegment_069_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 684 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 684 18 18, g32p_row19_traceSegment_069_0684_0018, g32p_row19_traceSegment_069_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 648 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 648 36 36, g32p_row19_traceSegment_069_0648_0036, g32p_row19_traceSegment_069_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 576 144 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 576 72 72, g32p_row19_traceSegment_069_0576_0072, g32p_row19_traceSegment_069_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 720 9 9, g32p_row19_traceSegment_069_0720_0009, g32p_row19_traceSegment_069_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 738 9 9, g32p_row19_traceSegment_069_0738_0009, g32p_row19_traceSegment_069_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 720 18 18, g32p_row19_traceSegment_069_0720_0018, g32p_row19_traceSegment_069_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 765 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 756 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 756 9 9, g32p_row19_traceSegment_069_0756_0009, g32p_row19_traceSegment_069_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 774 9 9, g32p_row19_traceSegment_069_0774_0009, g32p_row19_traceSegment_069_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 756 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 756 18 18, g32p_row19_traceSegment_069_0756_0018, g32p_row19_traceSegment_069_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 720 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 720 36 36, g32p_row19_traceSegment_069_0720_0036, g32p_row19_traceSegment_069_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 801 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 792 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 792 9 9, g32p_row19_traceSegment_069_0792_0009, g32p_row19_traceSegment_069_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 810 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 810 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 810 9 9, g32p_row19_traceSegment_069_0810_0009, g32p_row19_traceSegment_069_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 792 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 792 18 18, g32p_row19_traceSegment_069_0792_0018, g32p_row19_traceSegment_069_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 828 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 828 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 828 9 9, g32p_row19_traceSegment_069_0828_0009, g32p_row19_traceSegment_069_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 846 9 9, g32p_row19_traceSegment_069_0846_0009, g32p_row19_traceSegment_069_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 828 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 828 18 18, g32p_row19_traceSegment_069_0828_0018, g32p_row19_traceSegment_069_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 792 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 792 36 36, g32p_row19_traceSegment_069_0792_0036, g32p_row19_traceSegment_069_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 720 144 = [6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 720 72 72, g32p_row19_traceSegment_069_0720_0072, g32p_row19_traceSegment_069_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_069 576 288 = [10, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 576 144 144, g32p_row19_traceSegment_069_0576_0144, g32p_row19_traceSegment_069_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 864 9 9, g32p_row19_traceSegment_069_0864_0009, g32p_row19_traceSegment_069_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 882 9 9, g32p_row19_traceSegment_069_0882_0009, g32p_row19_traceSegment_069_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 864 18 18, g32p_row19_traceSegment_069_0864_0018, g32p_row19_traceSegment_069_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 900 9 9, g32p_row19_traceSegment_069_0900_0009, g32p_row19_traceSegment_069_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 918 9 9, g32p_row19_traceSegment_069_0918_0009, g32p_row19_traceSegment_069_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 900 18 18, g32p_row19_traceSegment_069_0900_0018, g32p_row19_traceSegment_069_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 864 36 36, g32p_row19_traceSegment_069_0864_0036, g32p_row19_traceSegment_069_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 945 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 936 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 936 9 9, g32p_row19_traceSegment_069_0936_0009, g32p_row19_traceSegment_069_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 954 9 9, g32p_row19_traceSegment_069_0954_0009, g32p_row19_traceSegment_069_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 936 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 936 18 18, g32p_row19_traceSegment_069_0936_0018, g32p_row19_traceSegment_069_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 972 9 9, g32p_row19_traceSegment_069_0972_0009, g32p_row19_traceSegment_069_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 990 9 9, g32p_row19_traceSegment_069_0990_0009, g32p_row19_traceSegment_069_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 972 18 18, g32p_row19_traceSegment_069_0972_0018, g32p_row19_traceSegment_069_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 936 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 936 36 36, g32p_row19_traceSegment_069_0936_0036, g32p_row19_traceSegment_069_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 864 144 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 864 72 72, g32p_row19_traceSegment_069_0864_0072, g32p_row19_traceSegment_069_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1008 9 9, g32p_row19_traceSegment_069_1008_0009, g32p_row19_traceSegment_069_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1035 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1026 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1026 9 9, g32p_row19_traceSegment_069_1026_0009, g32p_row19_traceSegment_069_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 1008 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1008 18 18, g32p_row19_traceSegment_069_1008_0018, g32p_row19_traceSegment_069_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1044 9 9, g32p_row19_traceSegment_069_1044_0009, g32p_row19_traceSegment_069_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1062 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1071 9 = [4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1062 18 = [5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1062 9 9, g32p_row19_traceSegment_069_1062_0009, g32p_row19_traceSegment_069_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 1044 36 = [5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1044 18 18, g32p_row19_traceSegment_069_1044_0018, g32p_row19_traceSegment_069_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 1008 72 = [5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1008 36 36, g32p_row19_traceSegment_069_1008_0036, g32p_row19_traceSegment_069_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1080 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1089 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1080 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1080 9 9, g32p_row19_traceSegment_069_1080_0009, g32p_row19_traceSegment_069_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1098 9 = [4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1098 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1098 9 9, g32p_row19_traceSegment_069_1098_0009, g32p_row19_traceSegment_069_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 1080 36 = [7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1080 18 18, g32p_row19_traceSegment_069_1080_0018, g32p_row19_traceSegment_069_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1116 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1125 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1116 18 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1116 9 9, g32p_row19_traceSegment_069_1116_0009, g32p_row19_traceSegment_069_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1134 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_069 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_069_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_069 1134 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1134 9 9, g32p_row19_traceSegment_069_1134_0009, g32p_row19_traceSegment_069_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_069 1116 36 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1116 18 18, g32p_row19_traceSegment_069_1116_0018, g32p_row19_traceSegment_069_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_069 1080 72 = [11, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1080 36 36, g32p_row19_traceSegment_069_1080_0036, g32p_row19_traceSegment_069_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_069_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_069 1008 144 = [16, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 1008 72 72, g32p_row19_traceSegment_069_1008_0072, g32p_row19_traceSegment_069_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_069 864 288 = [16, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 864 144 144, g32p_row19_traceSegment_069_0864_0144, g32p_row19_traceSegment_069_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_069 576 576 = [26, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 576 288 288, g32p_row19_traceSegment_069_0576_0288, g32p_row19_traceSegment_069_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_069_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_069 0 1152 = [36, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_069 0 576 576, g32p_row19_traceSegment_069_0000_0576, g32p_row19_traceSegment_069_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 69 = [36, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_069_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_074 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 74 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_074_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 9 9, g32p_row19_traceSegment_074_0000_0009, g32p_row19_traceSegment_074_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 18 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 27 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 18 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 18 9 9, g32p_row19_traceSegment_074_0018_0009, g32p_row19_traceSegment_074_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 0 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 18 18, g32p_row19_traceSegment_074_0000_0018, g32p_row19_traceSegment_074_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 36 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 36 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 36 9 9, g32p_row19_traceSegment_074_0036_0009, g32p_row19_traceSegment_074_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 54 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 54 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 54 9 9, g32p_row19_traceSegment_074_0054_0009, g32p_row19_traceSegment_074_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 36 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 36 18 18, g32p_row19_traceSegment_074_0036_0018, g32p_row19_traceSegment_074_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 0 72 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 36 36, g32p_row19_traceSegment_074_0000_0036, g32p_row19_traceSegment_074_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 72 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 81 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 72 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 72 9 9, g32p_row19_traceSegment_074_0072_0009, g32p_row19_traceSegment_074_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 99 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 90 9 9, g32p_row19_traceSegment_074_0090_0009, g32p_row19_traceSegment_074_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 72 36 = [0, 0, 0, 0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 72 18 18, g32p_row19_traceSegment_074_0072_0018, g32p_row19_traceSegment_074_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 108 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 108 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 108 9 9, g32p_row19_traceSegment_074_0108_0009, g32p_row19_traceSegment_074_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 135 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 126 9 9, g32p_row19_traceSegment_074_0126_0009, g32p_row19_traceSegment_074_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 108 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 108 18 18, g32p_row19_traceSegment_074_0108_0018, g32p_row19_traceSegment_074_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 72 72 = [0, 0, 0, 0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 72 36 36, g32p_row19_traceSegment_074_0072_0036, g32p_row19_traceSegment_074_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 0 144 = [0, 0, 0, 0, 4, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 72 72, g32p_row19_traceSegment_074_0000_0072, g32p_row19_traceSegment_074_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 144 9 9, g32p_row19_traceSegment_074_0144_0009, g32p_row19_traceSegment_074_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 162 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 162 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 162 9 9, g32p_row19_traceSegment_074_0162_0009, g32p_row19_traceSegment_074_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 144 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 144 18 18, g32p_row19_traceSegment_074_0144_0018, g32p_row19_traceSegment_074_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 189 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 180 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 180 9 9, g32p_row19_traceSegment_074_0180_0009, g32p_row19_traceSegment_074_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 198 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 207 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 198 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 198 9 9, g32p_row19_traceSegment_074_0198_0009, g32p_row19_traceSegment_074_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 180 36 = [0, 0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 180 18 18, g32p_row19_traceSegment_074_0180_0018, g32p_row19_traceSegment_074_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 144 72 = [0, 0, 0, 0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 144 36 36, g32p_row19_traceSegment_074_0144_0036, g32p_row19_traceSegment_074_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 216 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 225 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 216 18 = [0, 0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 216 9 9, g32p_row19_traceSegment_074_0216_0009, g32p_row19_traceSegment_074_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 234 9 9, g32p_row19_traceSegment_074_0234_0009, g32p_row19_traceSegment_074_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 216 36 = [0, 0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 216 18 18, g32p_row19_traceSegment_074_0216_0018, g32p_row19_traceSegment_074_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 252 9 9, g32p_row19_traceSegment_074_0252_0009, g32p_row19_traceSegment_074_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 270 9 9, g32p_row19_traceSegment_074_0270_0009, g32p_row19_traceSegment_074_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 252 18 18, g32p_row19_traceSegment_074_0252_0018, g32p_row19_traceSegment_074_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 216 72 = [0, 0, 0, 0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 216 36 36, g32p_row19_traceSegment_074_0216_0036, g32p_row19_traceSegment_074_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 144 144 = [0, 0, 0, 0, 4, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 144 72 72, g32p_row19_traceSegment_074_0144_0072, g32p_row19_traceSegment_074_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_074 0 288 = [0, 0, 0, 0, 8, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 144 144, g32p_row19_traceSegment_074_0000_0144, g32p_row19_traceSegment_074_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 297 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 288 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 288 9 9, g32p_row19_traceSegment_074_0288_0009, g32p_row19_traceSegment_074_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 306 9 9, g32p_row19_traceSegment_074_0306_0009, g32p_row19_traceSegment_074_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 288 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 288 18 18, g32p_row19_traceSegment_074_0288_0018, g32p_row19_traceSegment_074_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 324 9 9, g32p_row19_traceSegment_074_0324_0009, g32p_row19_traceSegment_074_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 342 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 342 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 342 9 9, g32p_row19_traceSegment_074_0342_0009, g32p_row19_traceSegment_074_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 324 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 324 18 18, g32p_row19_traceSegment_074_0324_0018, g32p_row19_traceSegment_074_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 288 72 = [0, 0, 0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 288 36 36, g32p_row19_traceSegment_074_0288_0036, g32p_row19_traceSegment_074_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 360 9 9, g32p_row19_traceSegment_074_0360_0009, g32p_row19_traceSegment_074_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 378 9 9, g32p_row19_traceSegment_074_0378_0009, g32p_row19_traceSegment_074_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 360 18 18, g32p_row19_traceSegment_074_0360_0018, g32p_row19_traceSegment_074_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 396 9 9, g32p_row19_traceSegment_074_0396_0009, g32p_row19_traceSegment_074_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 414 9 9, g32p_row19_traceSegment_074_0414_0009, g32p_row19_traceSegment_074_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 396 18 18, g32p_row19_traceSegment_074_0396_0018, g32p_row19_traceSegment_074_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 360 36 36, g32p_row19_traceSegment_074_0360_0036, g32p_row19_traceSegment_074_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 288 144 = [0, 0, 0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 288 72 72, g32p_row19_traceSegment_074_0288_0072, g32p_row19_traceSegment_074_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 432 9 9, g32p_row19_traceSegment_074_0432_0009, g32p_row19_traceSegment_074_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 450 9 9, g32p_row19_traceSegment_074_0450_0009, g32p_row19_traceSegment_074_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 432 18 18, g32p_row19_traceSegment_074_0432_0018, g32p_row19_traceSegment_074_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 468 9 9, g32p_row19_traceSegment_074_0468_0009, g32p_row19_traceSegment_074_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 486 9 9, g32p_row19_traceSegment_074_0486_0009, g32p_row19_traceSegment_074_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 468 18 18, g32p_row19_traceSegment_074_0468_0018, g32p_row19_traceSegment_074_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 432 36 36, g32p_row19_traceSegment_074_0432_0036, g32p_row19_traceSegment_074_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 513 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 504 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 504 9 9, g32p_row19_traceSegment_074_0504_0009, g32p_row19_traceSegment_074_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 522 9 9, g32p_row19_traceSegment_074_0522_0009, g32p_row19_traceSegment_074_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 504 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 504 18 18, g32p_row19_traceSegment_074_0504_0018, g32p_row19_traceSegment_074_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 549 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 540 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 540 9 9, g32p_row19_traceSegment_074_0540_0009, g32p_row19_traceSegment_074_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 558 9 9, g32p_row19_traceSegment_074_0558_0009, g32p_row19_traceSegment_074_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 540 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 540 18 18, g32p_row19_traceSegment_074_0540_0018, g32p_row19_traceSegment_074_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 504 72 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 504 36 36, g32p_row19_traceSegment_074_0504_0036, g32p_row19_traceSegment_074_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 432 144 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 432 72 72, g32p_row19_traceSegment_074_0432_0072, g32p_row19_traceSegment_074_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_074 288 288 = [0, 0, 0, 0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 288 144 144, g32p_row19_traceSegment_074_0288_0144, g32p_row19_traceSegment_074_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_074 0 576 = [0, 0, 0, 0, 10, 15] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 288 288, g32p_row19_traceSegment_074_0000_0288, g32p_row19_traceSegment_074_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 576 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 576 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 576 9 9, g32p_row19_traceSegment_074_0576_0009, g32p_row19_traceSegment_074_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 594 9 9, g32p_row19_traceSegment_074_0594_0009, g32p_row19_traceSegment_074_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 576 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 576 18 18, g32p_row19_traceSegment_074_0576_0018, g32p_row19_traceSegment_074_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 612 9 9, g32p_row19_traceSegment_074_0612_0009, g32p_row19_traceSegment_074_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 630 9 9, g32p_row19_traceSegment_074_0630_0009, g32p_row19_traceSegment_074_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 612 18 18, g32p_row19_traceSegment_074_0612_0018, g32p_row19_traceSegment_074_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 576 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 576 36 36, g32p_row19_traceSegment_074_0576_0036, g32p_row19_traceSegment_074_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 648 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 648 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 648 9 9, g32p_row19_traceSegment_074_0648_0009, g32p_row19_traceSegment_074_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 666 9 9, g32p_row19_traceSegment_074_0666_0009, g32p_row19_traceSegment_074_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 648 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 648 18 18, g32p_row19_traceSegment_074_0648_0018, g32p_row19_traceSegment_074_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 684 9 9, g32p_row19_traceSegment_074_0684_0009, g32p_row19_traceSegment_074_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 702 9 9, g32p_row19_traceSegment_074_0702_0009, g32p_row19_traceSegment_074_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 684 18 18, g32p_row19_traceSegment_074_0684_0018, g32p_row19_traceSegment_074_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 648 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 648 36 36, g32p_row19_traceSegment_074_0648_0036, g32p_row19_traceSegment_074_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 576 144 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 576 72 72, g32p_row19_traceSegment_074_0576_0072, g32p_row19_traceSegment_074_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 720 9 9, g32p_row19_traceSegment_074_0720_0009, g32p_row19_traceSegment_074_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 738 9 9, g32p_row19_traceSegment_074_0738_0009, g32p_row19_traceSegment_074_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 720 18 18, g32p_row19_traceSegment_074_0720_0018, g32p_row19_traceSegment_074_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 756 9 9, g32p_row19_traceSegment_074_0756_0009, g32p_row19_traceSegment_074_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 783 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 774 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 774 9 9, g32p_row19_traceSegment_074_0774_0009, g32p_row19_traceSegment_074_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 756 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 756 18 18, g32p_row19_traceSegment_074_0756_0018, g32p_row19_traceSegment_074_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 720 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 720 36 36, g32p_row19_traceSegment_074_0720_0036, g32p_row19_traceSegment_074_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 792 9 9, g32p_row19_traceSegment_074_0792_0009, g32p_row19_traceSegment_074_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 810 9 9, g32p_row19_traceSegment_074_0810_0009, g32p_row19_traceSegment_074_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 792 18 18, g32p_row19_traceSegment_074_0792_0018, g32p_row19_traceSegment_074_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 828 9 9, g32p_row19_traceSegment_074_0828_0009, g32p_row19_traceSegment_074_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 846 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 855 9 = [0, 0, 0, 0, 2, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 846 18 = [0, 0, 0, 0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 846 9 9, g32p_row19_traceSegment_074_0846_0009, g32p_row19_traceSegment_074_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 828 36 = [0, 0, 0, 0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 828 18 18, g32p_row19_traceSegment_074_0828_0018, g32p_row19_traceSegment_074_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 792 72 = [0, 0, 0, 0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 792 36 36, g32p_row19_traceSegment_074_0792_0036, g32p_row19_traceSegment_074_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 720 144 = [0, 0, 0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 720 72 72, g32p_row19_traceSegment_074_0720_0072, g32p_row19_traceSegment_074_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_074 576 288 = [0, 0, 0, 0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 576 144 144, g32p_row19_traceSegment_074_0576_0144, g32p_row19_traceSegment_074_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 864 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 873 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 864 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 864 9 9, g32p_row19_traceSegment_074_0864_0009, g32p_row19_traceSegment_074_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 882 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 891 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 882 18 = [0, 0, 0, 0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 882 9 9, g32p_row19_traceSegment_074_0882_0009, g32p_row19_traceSegment_074_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 864 36 = [0, 0, 0, 0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 864 18 18, g32p_row19_traceSegment_074_0864_0018, g32p_row19_traceSegment_074_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 900 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 909 9 = [0, 0, 0, 0, 1, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 900 18 = [0, 0, 0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 900 9 9, g32p_row19_traceSegment_074_0900_0009, g32p_row19_traceSegment_074_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 927 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 918 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 918 9 9, g32p_row19_traceSegment_074_0918_0009, g32p_row19_traceSegment_074_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 900 36 = [0, 0, 0, 0, 5, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 900 18 18, g32p_row19_traceSegment_074_0900_0018, g32p_row19_traceSegment_074_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 864 72 = [0, 0, 0, 0, 9, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 864 36 36, g32p_row19_traceSegment_074_0864_0036, g32p_row19_traceSegment_074_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 936 9 9, g32p_row19_traceSegment_074_0936_0009, g32p_row19_traceSegment_074_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 963 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 954 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 954 9 9, g32p_row19_traceSegment_074_0954_0009, g32p_row19_traceSegment_074_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 936 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 936 18 18, g32p_row19_traceSegment_074_0936_0018, g32p_row19_traceSegment_074_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 972 9 = [0, 0, 0, 0, 1, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 972 18 = [0, 0, 0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 972 9 9, g32p_row19_traceSegment_074_0972_0009, g32p_row19_traceSegment_074_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 990 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 990 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 990 9 9, g32p_row19_traceSegment_074_0990_0009, g32p_row19_traceSegment_074_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 972 36 = [0, 0, 0, 0, 3, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 972 18 18, g32p_row19_traceSegment_074_0972_0018, g32p_row19_traceSegment_074_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 936 72 = [0, 0, 0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 936 36 36, g32p_row19_traceSegment_074_0936_0036, g32p_row19_traceSegment_074_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 864 144 = [0, 0, 0, 0, 13, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 864 72 72, g32p_row19_traceSegment_074_0864_0072, g32p_row19_traceSegment_074_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1008 9 9, g32p_row19_traceSegment_074_1008_0009, g32p_row19_traceSegment_074_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1026 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1026 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1026 9 9, g32p_row19_traceSegment_074_1026_0009, g32p_row19_traceSegment_074_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 1008 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1008 18 18, g32p_row19_traceSegment_074_1008_0018, g32p_row19_traceSegment_074_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1044 9 = [0, 0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1053 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1044 18 = [0, 0, 0, 0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1044 9 9, g32p_row19_traceSegment_074_1044_0009, g32p_row19_traceSegment_074_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1062 9 9, g32p_row19_traceSegment_074_1062_0009, g32p_row19_traceSegment_074_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 1044 36 = [0, 0, 0, 0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1044 18 18, g32p_row19_traceSegment_074_1044_0018, g32p_row19_traceSegment_074_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 1008 72 = [0, 0, 0, 0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1008 36 36, g32p_row19_traceSegment_074_1008_0036, g32p_row19_traceSegment_074_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1080 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1080 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1080 9 9, g32p_row19_traceSegment_074_1080_0009, g32p_row19_traceSegment_074_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1098 9 9, g32p_row19_traceSegment_074_1098_0009, g32p_row19_traceSegment_074_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 1080 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1080 18 18, g32p_row19_traceSegment_074_1080_0018, g32p_row19_traceSegment_074_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1116 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1116 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1116 9 9, g32p_row19_traceSegment_074_1116_0009, g32p_row19_traceSegment_074_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1134 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_074 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_074_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_074 1134 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1134 9 9, g32p_row19_traceSegment_074_1134_0009, g32p_row19_traceSegment_074_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_074 1116 36 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1116 18 18, g32p_row19_traceSegment_074_1116_0018, g32p_row19_traceSegment_074_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_074 1080 72 = [0, 0, 0, 0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1080 36 36, g32p_row19_traceSegment_074_1080_0036, g32p_row19_traceSegment_074_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_074_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_074 1008 144 = [0, 0, 0, 0, 5, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 1008 72 72, g32p_row19_traceSegment_074_1008_0072, g32p_row19_traceSegment_074_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_074 864 288 = [0, 0, 0, 0, 18, 13] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 864 144 144, g32p_row19_traceSegment_074_0864_0144, g32p_row19_traceSegment_074_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_074 576 576 = [0, 0, 0, 0, 22, 17] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 576 288 288, g32p_row19_traceSegment_074_0576_0288, g32p_row19_traceSegment_074_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_074_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_074 0 1152 = [0, 0, 0, 0, 32, 32] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_074 0 576 576, g32p_row19_traceSegment_074_0000_0576, g32p_row19_traceSegment_074_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 74 = [0, 0, 0, 0, 32, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_074_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_078_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 0 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 9 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 0 18 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 9 9, g32p_row19_traceSegment_078_0000_0009, g32p_row19_traceSegment_078_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 18 9 9, g32p_row19_traceSegment_078_0018_0009, g32p_row19_traceSegment_078_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 0 36 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 18 18, g32p_row19_traceSegment_078_0000_0018, g32p_row19_traceSegment_078_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 36 9 9, g32p_row19_traceSegment_078_0036_0009, g32p_row19_traceSegment_078_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 54 9 9, g32p_row19_traceSegment_078_0054_0009, g32p_row19_traceSegment_078_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 36 18 18, g32p_row19_traceSegment_078_0036_0018, g32p_row19_traceSegment_078_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 0 72 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 36 36, g32p_row19_traceSegment_078_0000_0036, g32p_row19_traceSegment_078_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 72 9 9, g32p_row19_traceSegment_078_0072_0009, g32p_row19_traceSegment_078_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 90 9 9, g32p_row19_traceSegment_078_0090_0009, g32p_row19_traceSegment_078_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 72 18 18, g32p_row19_traceSegment_078_0072_0018, g32p_row19_traceSegment_078_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 108 9 9, g32p_row19_traceSegment_078_0108_0009, g32p_row19_traceSegment_078_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 126 9 9, g32p_row19_traceSegment_078_0126_0009, g32p_row19_traceSegment_078_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 108 18 18, g32p_row19_traceSegment_078_0108_0018, g32p_row19_traceSegment_078_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 72 36 36, g32p_row19_traceSegment_078_0072_0036, g32p_row19_traceSegment_078_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 0 144 = [0, 0, 3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 72 72, g32p_row19_traceSegment_078_0000_0072, g32p_row19_traceSegment_078_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 144 9 9, g32p_row19_traceSegment_078_0144_0009, g32p_row19_traceSegment_078_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 162 9 9, g32p_row19_traceSegment_078_0162_0009, g32p_row19_traceSegment_078_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 144 18 18, g32p_row19_traceSegment_078_0144_0018, g32p_row19_traceSegment_078_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 180 9 9, g32p_row19_traceSegment_078_0180_0009, g32p_row19_traceSegment_078_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 198 9 9, g32p_row19_traceSegment_078_0198_0009, g32p_row19_traceSegment_078_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 180 18 18, g32p_row19_traceSegment_078_0180_0018, g32p_row19_traceSegment_078_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 144 36 36, g32p_row19_traceSegment_078_0144_0036, g32p_row19_traceSegment_078_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 225 9 = [0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 216 18 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 216 9 9, g32p_row19_traceSegment_078_0216_0009, g32p_row19_traceSegment_078_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 243 9 = [0, 0, 1, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 234 18 = [0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 234 9 9, g32p_row19_traceSegment_078_0234_0009, g32p_row19_traceSegment_078_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 216 36 = [0, 0, 2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 216 18 18, g32p_row19_traceSegment_078_0216_0018, g32p_row19_traceSegment_078_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 252 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 252 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 252 9 9, g32p_row19_traceSegment_078_0252_0009, g32p_row19_traceSegment_078_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 270 9 9, g32p_row19_traceSegment_078_0270_0009, g32p_row19_traceSegment_078_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 252 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 252 18 18, g32p_row19_traceSegment_078_0252_0018, g32p_row19_traceSegment_078_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 216 72 = [0, 0, 2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 216 36 36, g32p_row19_traceSegment_078_0216_0036, g32p_row19_traceSegment_078_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 144 144 = [0, 0, 2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 144 72 72, g32p_row19_traceSegment_078_0144_0072, g32p_row19_traceSegment_078_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_078 0 288 = [0, 0, 5, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 144 144, g32p_row19_traceSegment_078_0000_0144, g32p_row19_traceSegment_078_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 288 9 = [0, 0, 1, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 288 18 = [0, 0, 1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 288 9 9, g32p_row19_traceSegment_078_0288_0009, g32p_row19_traceSegment_078_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 306 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 315 9 = [0, 0, 1, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 306 18 = [0, 0, 1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 306 9 9, g32p_row19_traceSegment_078_0306_0009, g32p_row19_traceSegment_078_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 288 36 = [0, 0, 2, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 288 18 18, g32p_row19_traceSegment_078_0288_0018, g32p_row19_traceSegment_078_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 324 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 333 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 324 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 324 9 9, g32p_row19_traceSegment_078_0324_0009, g32p_row19_traceSegment_078_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 342 9 9, g32p_row19_traceSegment_078_0342_0009, g32p_row19_traceSegment_078_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 324 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 324 18 18, g32p_row19_traceSegment_078_0324_0018, g32p_row19_traceSegment_078_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 288 72 = [0, 0, 2, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 288 36 36, g32p_row19_traceSegment_078_0288_0036, g32p_row19_traceSegment_078_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 360 9 9, g32p_row19_traceSegment_078_0360_0009, g32p_row19_traceSegment_078_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 378 9 9, g32p_row19_traceSegment_078_0378_0009, g32p_row19_traceSegment_078_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 360 18 18, g32p_row19_traceSegment_078_0360_0018, g32p_row19_traceSegment_078_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 396 9 9, g32p_row19_traceSegment_078_0396_0009, g32p_row19_traceSegment_078_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 414 9 9, g32p_row19_traceSegment_078_0414_0009, g32p_row19_traceSegment_078_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 396 18 18, g32p_row19_traceSegment_078_0396_0018, g32p_row19_traceSegment_078_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 360 36 36, g32p_row19_traceSegment_078_0360_0036, g32p_row19_traceSegment_078_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 288 144 = [0, 0, 2, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 288 72 72, g32p_row19_traceSegment_078_0288_0072, g32p_row19_traceSegment_078_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 432 9 9, g32p_row19_traceSegment_078_0432_0009, g32p_row19_traceSegment_078_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 450 9 9, g32p_row19_traceSegment_078_0450_0009, g32p_row19_traceSegment_078_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 432 18 18, g32p_row19_traceSegment_078_0432_0018, g32p_row19_traceSegment_078_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 468 9 9, g32p_row19_traceSegment_078_0468_0009, g32p_row19_traceSegment_078_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 486 9 9, g32p_row19_traceSegment_078_0486_0009, g32p_row19_traceSegment_078_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 468 18 18, g32p_row19_traceSegment_078_0468_0018, g32p_row19_traceSegment_078_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 432 36 36, g32p_row19_traceSegment_078_0432_0036, g32p_row19_traceSegment_078_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 504 9 9, g32p_row19_traceSegment_078_0504_0009, g32p_row19_traceSegment_078_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 522 9 9, g32p_row19_traceSegment_078_0522_0009, g32p_row19_traceSegment_078_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 504 18 18, g32p_row19_traceSegment_078_0504_0018, g32p_row19_traceSegment_078_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 540 9 9, g32p_row19_traceSegment_078_0540_0009, g32p_row19_traceSegment_078_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 558 9 9, g32p_row19_traceSegment_078_0558_0009, g32p_row19_traceSegment_078_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 540 18 18, g32p_row19_traceSegment_078_0540_0018, g32p_row19_traceSegment_078_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 504 36 36, g32p_row19_traceSegment_078_0504_0036, g32p_row19_traceSegment_078_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 432 72 72, g32p_row19_traceSegment_078_0432_0072, g32p_row19_traceSegment_078_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_078 288 288 = [0, 0, 2, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 288 144 144, g32p_row19_traceSegment_078_0288_0144, g32p_row19_traceSegment_078_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_078 0 576 = [0, 0, 7, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 288 288, g32p_row19_traceSegment_078_0000_0288, g32p_row19_traceSegment_078_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 576 9 9, g32p_row19_traceSegment_078_0576_0009, g32p_row19_traceSegment_078_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 594 9 9, g32p_row19_traceSegment_078_0594_0009, g32p_row19_traceSegment_078_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 576 18 18, g32p_row19_traceSegment_078_0576_0018, g32p_row19_traceSegment_078_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 612 9 9, g32p_row19_traceSegment_078_0612_0009, g32p_row19_traceSegment_078_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 630 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 630 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 630 9 9, g32p_row19_traceSegment_078_0630_0009, g32p_row19_traceSegment_078_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 612 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 612 18 18, g32p_row19_traceSegment_078_0612_0018, g32p_row19_traceSegment_078_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 576 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 576 36 36, g32p_row19_traceSegment_078_0576_0036, g32p_row19_traceSegment_078_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 648 9 9, g32p_row19_traceSegment_078_0648_0009, g32p_row19_traceSegment_078_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 666 9 9, g32p_row19_traceSegment_078_0666_0009, g32p_row19_traceSegment_078_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 648 18 18, g32p_row19_traceSegment_078_0648_0018, g32p_row19_traceSegment_078_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 684 9 9, g32p_row19_traceSegment_078_0684_0009, g32p_row19_traceSegment_078_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 702 9 9, g32p_row19_traceSegment_078_0702_0009, g32p_row19_traceSegment_078_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 684 18 18, g32p_row19_traceSegment_078_0684_0018, g32p_row19_traceSegment_078_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 648 36 36, g32p_row19_traceSegment_078_0648_0036, g32p_row19_traceSegment_078_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 576 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 576 72 72, g32p_row19_traceSegment_078_0576_0072, g32p_row19_traceSegment_078_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 720 9 9, g32p_row19_traceSegment_078_0720_0009, g32p_row19_traceSegment_078_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 738 9 9, g32p_row19_traceSegment_078_0738_0009, g32p_row19_traceSegment_078_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 720 18 18, g32p_row19_traceSegment_078_0720_0018, g32p_row19_traceSegment_078_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 756 9 9, g32p_row19_traceSegment_078_0756_0009, g32p_row19_traceSegment_078_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 774 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 783 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 774 18 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 774 9 9, g32p_row19_traceSegment_078_0774_0009, g32p_row19_traceSegment_078_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 756 36 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 756 18 18, g32p_row19_traceSegment_078_0756_0018, g32p_row19_traceSegment_078_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 720 72 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 720 36 36, g32p_row19_traceSegment_078_0720_0036, g32p_row19_traceSegment_078_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 792 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 801 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 792 18 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 792 9 9, g32p_row19_traceSegment_078_0792_0009, g32p_row19_traceSegment_078_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 810 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 810 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 810 9 9, g32p_row19_traceSegment_078_0810_0009, g32p_row19_traceSegment_078_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 792 36 = [0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 792 18 18, g32p_row19_traceSegment_078_0792_0018, g32p_row19_traceSegment_078_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 828 9 9, g32p_row19_traceSegment_078_0828_0009, g32p_row19_traceSegment_078_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 846 9 9, g32p_row19_traceSegment_078_0846_0009, g32p_row19_traceSegment_078_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 828 18 18, g32p_row19_traceSegment_078_0828_0018, g32p_row19_traceSegment_078_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 792 72 = [0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 792 36 36, g32p_row19_traceSegment_078_0792_0036, g32p_row19_traceSegment_078_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 720 144 = [0, 0, 3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 720 72 72, g32p_row19_traceSegment_078_0720_0072, g32p_row19_traceSegment_078_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_078 576 288 = [0, 0, 4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 576 144 144, g32p_row19_traceSegment_078_0576_0144, g32p_row19_traceSegment_078_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 864 9 9, g32p_row19_traceSegment_078_0864_0009, g32p_row19_traceSegment_078_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 882 9 9, g32p_row19_traceSegment_078_0882_0009, g32p_row19_traceSegment_078_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 864 18 18, g32p_row19_traceSegment_078_0864_0018, g32p_row19_traceSegment_078_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 900 9 9, g32p_row19_traceSegment_078_0900_0009, g32p_row19_traceSegment_078_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 918 9 9, g32p_row19_traceSegment_078_0918_0009, g32p_row19_traceSegment_078_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 900 18 18, g32p_row19_traceSegment_078_0900_0018, g32p_row19_traceSegment_078_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 864 36 36, g32p_row19_traceSegment_078_0864_0036, g32p_row19_traceSegment_078_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 936 9 9, g32p_row19_traceSegment_078_0936_0009, g32p_row19_traceSegment_078_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 963 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 954 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 954 9 9, g32p_row19_traceSegment_078_0954_0009, g32p_row19_traceSegment_078_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 936 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 936 18 18, g32p_row19_traceSegment_078_0936_0018, g32p_row19_traceSegment_078_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 972 9 9, g32p_row19_traceSegment_078_0972_0009, g32p_row19_traceSegment_078_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 990 9 9, g32p_row19_traceSegment_078_0990_0009, g32p_row19_traceSegment_078_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 972 18 18, g32p_row19_traceSegment_078_0972_0018, g32p_row19_traceSegment_078_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 936 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 936 36 36, g32p_row19_traceSegment_078_0936_0036, g32p_row19_traceSegment_078_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 864 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 864 72 72, g32p_row19_traceSegment_078_0864_0072, g32p_row19_traceSegment_078_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1017 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1008 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1008 9 9, g32p_row19_traceSegment_078_1008_0009, g32p_row19_traceSegment_078_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1035 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1026 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1026 9 9, g32p_row19_traceSegment_078_1026_0009, g32p_row19_traceSegment_078_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 1008 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1008 18 18, g32p_row19_traceSegment_078_1008_0018, g32p_row19_traceSegment_078_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1044 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1044 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1044 9 9, g32p_row19_traceSegment_078_1044_0009, g32p_row19_traceSegment_078_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1062 9 9, g32p_row19_traceSegment_078_1062_0009, g32p_row19_traceSegment_078_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 1044 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1044 18 18, g32p_row19_traceSegment_078_1044_0018, g32p_row19_traceSegment_078_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 1008 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1008 36 36, g32p_row19_traceSegment_078_1008_0036, g32p_row19_traceSegment_078_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1080 9 9, g32p_row19_traceSegment_078_1080_0009, g32p_row19_traceSegment_078_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1098 9 9, g32p_row19_traceSegment_078_1098_0009, g32p_row19_traceSegment_078_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1080 18 18, g32p_row19_traceSegment_078_1080_0018, g32p_row19_traceSegment_078_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1116 9 9, g32p_row19_traceSegment_078_1116_0009, g32p_row19_traceSegment_078_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_078 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_078_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_078 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1134 9 9, g32p_row19_traceSegment_078_1134_0009, g32p_row19_traceSegment_078_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_078 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1116 18 18, g32p_row19_traceSegment_078_1116_0018, g32p_row19_traceSegment_078_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_078 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1080 36 36, g32p_row19_traceSegment_078_1080_0036, g32p_row19_traceSegment_078_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_078_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_078 1008 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 1008 72 72, g32p_row19_traceSegment_078_1008_0072, g32p_row19_traceSegment_078_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_078 864 288 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 864 144 144, g32p_row19_traceSegment_078_0864_0144, g32p_row19_traceSegment_078_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_078 576 576 = [0, 0, 9, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 576 288 288, g32p_row19_traceSegment_078_0576_0288, g32p_row19_traceSegment_078_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_078_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_078 0 1152 = [0, 0, 16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_078 0 576 576, g32p_row19_traceSegment_078_0000_0576, g32p_row19_traceSegment_078_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 78 = [0, 0, 16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_078_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_082_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 9 9, g32p_row19_traceSegment_082_0000_0009, g32p_row19_traceSegment_082_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 18 9 9, g32p_row19_traceSegment_082_0018_0009, g32p_row19_traceSegment_082_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 18 18, g32p_row19_traceSegment_082_0000_0018, g32p_row19_traceSegment_082_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 36 9 9, g32p_row19_traceSegment_082_0036_0009, g32p_row19_traceSegment_082_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 54 9 9, g32p_row19_traceSegment_082_0054_0009, g32p_row19_traceSegment_082_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 36 18 18, g32p_row19_traceSegment_082_0036_0018, g32p_row19_traceSegment_082_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 36 36, g32p_row19_traceSegment_082_0000_0036, g32p_row19_traceSegment_082_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 72 9 9, g32p_row19_traceSegment_082_0072_0009, g32p_row19_traceSegment_082_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 90 9 9, g32p_row19_traceSegment_082_0090_0009, g32p_row19_traceSegment_082_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 72 18 18, g32p_row19_traceSegment_082_0072_0018, g32p_row19_traceSegment_082_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 108 9 9, g32p_row19_traceSegment_082_0108_0009, g32p_row19_traceSegment_082_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 126 9 9, g32p_row19_traceSegment_082_0126_0009, g32p_row19_traceSegment_082_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 108 18 18, g32p_row19_traceSegment_082_0108_0018, g32p_row19_traceSegment_082_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 72 36 36, g32p_row19_traceSegment_082_0072_0036, g32p_row19_traceSegment_082_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 72 72, g32p_row19_traceSegment_082_0000_0072, g32p_row19_traceSegment_082_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 153 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 144 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 144 9 9, g32p_row19_traceSegment_082_0144_0009, g32p_row19_traceSegment_082_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 162 9 9, g32p_row19_traceSegment_082_0162_0009, g32p_row19_traceSegment_082_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 144 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 144 18 18, g32p_row19_traceSegment_082_0144_0018, g32p_row19_traceSegment_082_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 180 9 9, g32p_row19_traceSegment_082_0180_0009, g32p_row19_traceSegment_082_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 198 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 198 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 198 9 9, g32p_row19_traceSegment_082_0198_0009, g32p_row19_traceSegment_082_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 180 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 180 18 18, g32p_row19_traceSegment_082_0180_0018, g32p_row19_traceSegment_082_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 144 72 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 144 36 36, g32p_row19_traceSegment_082_0144_0036, g32p_row19_traceSegment_082_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 216 9 9, g32p_row19_traceSegment_082_0216_0009, g32p_row19_traceSegment_082_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 234 9 9, g32p_row19_traceSegment_082_0234_0009, g32p_row19_traceSegment_082_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 216 18 18, g32p_row19_traceSegment_082_0216_0018, g32p_row19_traceSegment_082_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 252 9 9, g32p_row19_traceSegment_082_0252_0009, g32p_row19_traceSegment_082_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 270 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 270 9 9, g32p_row19_traceSegment_082_0270_0009, g32p_row19_traceSegment_082_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 252 18 18, g32p_row19_traceSegment_082_0252_0018, g32p_row19_traceSegment_082_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 216 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 216 36 36, g32p_row19_traceSegment_082_0216_0036, g32p_row19_traceSegment_082_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 144 144 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 144 72 72, g32p_row19_traceSegment_082_0144_0072, g32p_row19_traceSegment_082_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_082 0 288 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 144 144, g32p_row19_traceSegment_082_0000_0144, g32p_row19_traceSegment_082_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 297 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 288 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 288 9 9, g32p_row19_traceSegment_082_0288_0009, g32p_row19_traceSegment_082_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 306 9 9, g32p_row19_traceSegment_082_0306_0009, g32p_row19_traceSegment_082_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 288 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 288 18 18, g32p_row19_traceSegment_082_0288_0018, g32p_row19_traceSegment_082_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 324 9 9, g32p_row19_traceSegment_082_0324_0009, g32p_row19_traceSegment_082_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 351 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 342 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 342 9 9, g32p_row19_traceSegment_082_0342_0009, g32p_row19_traceSegment_082_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 324 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 324 18 18, g32p_row19_traceSegment_082_0324_0018, g32p_row19_traceSegment_082_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 288 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 288 36 36, g32p_row19_traceSegment_082_0288_0036, g32p_row19_traceSegment_082_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 360 9 9, g32p_row19_traceSegment_082_0360_0009, g32p_row19_traceSegment_082_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 387 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 378 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 378 9 9, g32p_row19_traceSegment_082_0378_0009, g32p_row19_traceSegment_082_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 360 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 360 18 18, g32p_row19_traceSegment_082_0360_0018, g32p_row19_traceSegment_082_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 396 9 9, g32p_row19_traceSegment_082_0396_0009, g32p_row19_traceSegment_082_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 414 9 9, g32p_row19_traceSegment_082_0414_0009, g32p_row19_traceSegment_082_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 396 18 18, g32p_row19_traceSegment_082_0396_0018, g32p_row19_traceSegment_082_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 360 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 360 36 36, g32p_row19_traceSegment_082_0360_0036, g32p_row19_traceSegment_082_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 288 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 288 72 72, g32p_row19_traceSegment_082_0288_0072, g32p_row19_traceSegment_082_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 432 9 9, g32p_row19_traceSegment_082_0432_0009, g32p_row19_traceSegment_082_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 450 9 9, g32p_row19_traceSegment_082_0450_0009, g32p_row19_traceSegment_082_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 432 18 18, g32p_row19_traceSegment_082_0432_0018, g32p_row19_traceSegment_082_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 468 9 9, g32p_row19_traceSegment_082_0468_0009, g32p_row19_traceSegment_082_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 486 9 9, g32p_row19_traceSegment_082_0486_0009, g32p_row19_traceSegment_082_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 468 18 18, g32p_row19_traceSegment_082_0468_0018, g32p_row19_traceSegment_082_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 432 36 36, g32p_row19_traceSegment_082_0432_0036, g32p_row19_traceSegment_082_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 504 9 9, g32p_row19_traceSegment_082_0504_0009, g32p_row19_traceSegment_082_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 522 9 9, g32p_row19_traceSegment_082_0522_0009, g32p_row19_traceSegment_082_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 504 18 18, g32p_row19_traceSegment_082_0504_0018, g32p_row19_traceSegment_082_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 540 9 9, g32p_row19_traceSegment_082_0540_0009, g32p_row19_traceSegment_082_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 558 9 9, g32p_row19_traceSegment_082_0558_0009, g32p_row19_traceSegment_082_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 540 18 18, g32p_row19_traceSegment_082_0540_0018, g32p_row19_traceSegment_082_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 504 36 36, g32p_row19_traceSegment_082_0504_0036, g32p_row19_traceSegment_082_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 432 72 72, g32p_row19_traceSegment_082_0432_0072, g32p_row19_traceSegment_082_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_082 288 288 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 288 144 144, g32p_row19_traceSegment_082_0288_0144, g32p_row19_traceSegment_082_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_082 0 576 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 288 288, g32p_row19_traceSegment_082_0000_0288, g32p_row19_traceSegment_082_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 576 9 9, g32p_row19_traceSegment_082_0576_0009, g32p_row19_traceSegment_082_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 594 9 9, g32p_row19_traceSegment_082_0594_0009, g32p_row19_traceSegment_082_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 576 18 18, g32p_row19_traceSegment_082_0576_0018, g32p_row19_traceSegment_082_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 612 9 9, g32p_row19_traceSegment_082_0612_0009, g32p_row19_traceSegment_082_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 630 9 9, g32p_row19_traceSegment_082_0630_0009, g32p_row19_traceSegment_082_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 612 18 18, g32p_row19_traceSegment_082_0612_0018, g32p_row19_traceSegment_082_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 576 36 36, g32p_row19_traceSegment_082_0576_0036, g32p_row19_traceSegment_082_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 648 9 9, g32p_row19_traceSegment_082_0648_0009, g32p_row19_traceSegment_082_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 666 9 9, g32p_row19_traceSegment_082_0666_0009, g32p_row19_traceSegment_082_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 648 18 18, g32p_row19_traceSegment_082_0648_0018, g32p_row19_traceSegment_082_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 684 9 9, g32p_row19_traceSegment_082_0684_0009, g32p_row19_traceSegment_082_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 702 9 9, g32p_row19_traceSegment_082_0702_0009, g32p_row19_traceSegment_082_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 684 18 18, g32p_row19_traceSegment_082_0684_0018, g32p_row19_traceSegment_082_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 648 36 36, g32p_row19_traceSegment_082_0648_0036, g32p_row19_traceSegment_082_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 576 72 72, g32p_row19_traceSegment_082_0576_0072, g32p_row19_traceSegment_082_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 720 9 9, g32p_row19_traceSegment_082_0720_0009, g32p_row19_traceSegment_082_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 738 9 9, g32p_row19_traceSegment_082_0738_0009, g32p_row19_traceSegment_082_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 720 18 18, g32p_row19_traceSegment_082_0720_0018, g32p_row19_traceSegment_082_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 756 9 9, g32p_row19_traceSegment_082_0756_0009, g32p_row19_traceSegment_082_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 774 9 9, g32p_row19_traceSegment_082_0774_0009, g32p_row19_traceSegment_082_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 756 18 18, g32p_row19_traceSegment_082_0756_0018, g32p_row19_traceSegment_082_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 720 36 36, g32p_row19_traceSegment_082_0720_0036, g32p_row19_traceSegment_082_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 792 9 9, g32p_row19_traceSegment_082_0792_0009, g32p_row19_traceSegment_082_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 810 9 9, g32p_row19_traceSegment_082_0810_0009, g32p_row19_traceSegment_082_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 792 18 18, g32p_row19_traceSegment_082_0792_0018, g32p_row19_traceSegment_082_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 828 9 9, g32p_row19_traceSegment_082_0828_0009, g32p_row19_traceSegment_082_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 846 9 9, g32p_row19_traceSegment_082_0846_0009, g32p_row19_traceSegment_082_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 828 18 18, g32p_row19_traceSegment_082_0828_0018, g32p_row19_traceSegment_082_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 792 36 36, g32p_row19_traceSegment_082_0792_0036, g32p_row19_traceSegment_082_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 720 72 72, g32p_row19_traceSegment_082_0720_0072, g32p_row19_traceSegment_082_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_082 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 576 144 144, g32p_row19_traceSegment_082_0576_0144, g32p_row19_traceSegment_082_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 864 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 864 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 864 9 9, g32p_row19_traceSegment_082_0864_0009, g32p_row19_traceSegment_082_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 891 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 882 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 882 9 9, g32p_row19_traceSegment_082_0882_0009, g32p_row19_traceSegment_082_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 864 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 864 18 18, g32p_row19_traceSegment_082_0864_0018, g32p_row19_traceSegment_082_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 900 9 9, g32p_row19_traceSegment_082_0900_0009, g32p_row19_traceSegment_082_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 918 9 9, g32p_row19_traceSegment_082_0918_0009, g32p_row19_traceSegment_082_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 900 18 18, g32p_row19_traceSegment_082_0900_0018, g32p_row19_traceSegment_082_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 864 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 864 36 36, g32p_row19_traceSegment_082_0864_0036, g32p_row19_traceSegment_082_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 936 9 9, g32p_row19_traceSegment_082_0936_0009, g32p_row19_traceSegment_082_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 963 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 954 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 954 9 9, g32p_row19_traceSegment_082_0954_0009, g32p_row19_traceSegment_082_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 936 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 936 18 18, g32p_row19_traceSegment_082_0936_0018, g32p_row19_traceSegment_082_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 972 9 9, g32p_row19_traceSegment_082_0972_0009, g32p_row19_traceSegment_082_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 990 9 9, g32p_row19_traceSegment_082_0990_0009, g32p_row19_traceSegment_082_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 972 18 18, g32p_row19_traceSegment_082_0972_0018, g32p_row19_traceSegment_082_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 936 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 936 36 36, g32p_row19_traceSegment_082_0936_0036, g32p_row19_traceSegment_082_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 864 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 864 72 72, g32p_row19_traceSegment_082_0864_0072, g32p_row19_traceSegment_082_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1008 9 9, g32p_row19_traceSegment_082_1008_0009, g32p_row19_traceSegment_082_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1026 9 9, g32p_row19_traceSegment_082_1026_0009, g32p_row19_traceSegment_082_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1008 18 18, g32p_row19_traceSegment_082_1008_0018, g32p_row19_traceSegment_082_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1044 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1044 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1044 9 9, g32p_row19_traceSegment_082_1044_0009, g32p_row19_traceSegment_082_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1062 9 9, g32p_row19_traceSegment_082_1062_0009, g32p_row19_traceSegment_082_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 1044 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1044 18 18, g32p_row19_traceSegment_082_1044_0018, g32p_row19_traceSegment_082_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 1008 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1008 36 36, g32p_row19_traceSegment_082_1008_0036, g32p_row19_traceSegment_082_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1080 9 9, g32p_row19_traceSegment_082_1080_0009, g32p_row19_traceSegment_082_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1098 9 9, g32p_row19_traceSegment_082_1098_0009, g32p_row19_traceSegment_082_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1080 18 18, g32p_row19_traceSegment_082_1080_0018, g32p_row19_traceSegment_082_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1116 9 9, g32p_row19_traceSegment_082_1116_0009, g32p_row19_traceSegment_082_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_082 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_082_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_082 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1134 9 9, g32p_row19_traceSegment_082_1134_0009, g32p_row19_traceSegment_082_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_082 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1116 18 18, g32p_row19_traceSegment_082_1116_0018, g32p_row19_traceSegment_082_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_082 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1080 36 36, g32p_row19_traceSegment_082_1080_0036, g32p_row19_traceSegment_082_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_082_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_082 1008 144 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 1008 72 72, g32p_row19_traceSegment_082_1008_0072, g32p_row19_traceSegment_082_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_082 864 288 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 864 144 144, g32p_row19_traceSegment_082_0864_0144, g32p_row19_traceSegment_082_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_082 576 576 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 576 288 288, g32p_row19_traceSegment_082_0576_0288, g32p_row19_traceSegment_082_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_082_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_082 0 1152 = [0, 0, 2, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_082 0 576 576, g32p_row19_traceSegment_082_0000_0576, g32p_row19_traceSegment_082_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 82 = [0, 0, 2, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_082_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_083 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 83 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_083_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 0 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 9 9, g32p_row19_traceSegment_083_0000_0009, g32p_row19_traceSegment_083_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 18 9 9, g32p_row19_traceSegment_083_0018_0009, g32p_row19_traceSegment_083_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 18 18, g32p_row19_traceSegment_083_0000_0018, g32p_row19_traceSegment_083_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 36 9 9, g32p_row19_traceSegment_083_0036_0009, g32p_row19_traceSegment_083_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 54 9 9, g32p_row19_traceSegment_083_0054_0009, g32p_row19_traceSegment_083_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 36 18 18, g32p_row19_traceSegment_083_0036_0018, g32p_row19_traceSegment_083_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 36 36, g32p_row19_traceSegment_083_0000_0036, g32p_row19_traceSegment_083_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 72 9 9, g32p_row19_traceSegment_083_0072_0009, g32p_row19_traceSegment_083_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 90 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 90 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 90 9 9, g32p_row19_traceSegment_083_0090_0009, g32p_row19_traceSegment_083_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 72 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 72 18 18, g32p_row19_traceSegment_083_0072_0018, g32p_row19_traceSegment_083_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 108 9 9, g32p_row19_traceSegment_083_0108_0009, g32p_row19_traceSegment_083_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 135 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 126 9 9, g32p_row19_traceSegment_083_0126_0009, g32p_row19_traceSegment_083_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 108 18 18, g32p_row19_traceSegment_083_0108_0018, g32p_row19_traceSegment_083_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 72 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 72 36 36, g32p_row19_traceSegment_083_0072_0036, g32p_row19_traceSegment_083_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 0 144 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 72 72, g32p_row19_traceSegment_083_0000_0072, g32p_row19_traceSegment_083_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 144 9 9, g32p_row19_traceSegment_083_0144_0009, g32p_row19_traceSegment_083_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 162 9 9, g32p_row19_traceSegment_083_0162_0009, g32p_row19_traceSegment_083_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 144 18 18, g32p_row19_traceSegment_083_0144_0018, g32p_row19_traceSegment_083_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 180 9 9, g32p_row19_traceSegment_083_0180_0009, g32p_row19_traceSegment_083_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 198 9 9, g32p_row19_traceSegment_083_0198_0009, g32p_row19_traceSegment_083_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 180 18 18, g32p_row19_traceSegment_083_0180_0018, g32p_row19_traceSegment_083_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 144 36 36, g32p_row19_traceSegment_083_0144_0036, g32p_row19_traceSegment_083_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 216 9 9, g32p_row19_traceSegment_083_0216_0009, g32p_row19_traceSegment_083_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 234 9 9, g32p_row19_traceSegment_083_0234_0009, g32p_row19_traceSegment_083_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 216 18 18, g32p_row19_traceSegment_083_0216_0018, g32p_row19_traceSegment_083_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 252 9 9, g32p_row19_traceSegment_083_0252_0009, g32p_row19_traceSegment_083_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 270 9 9, g32p_row19_traceSegment_083_0270_0009, g32p_row19_traceSegment_083_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 252 18 18, g32p_row19_traceSegment_083_0252_0018, g32p_row19_traceSegment_083_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 216 36 36, g32p_row19_traceSegment_083_0216_0036, g32p_row19_traceSegment_083_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 144 72 72, g32p_row19_traceSegment_083_0144_0072, g32p_row19_traceSegment_083_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_083 0 288 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 144 144, g32p_row19_traceSegment_083_0000_0144, g32p_row19_traceSegment_083_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 288 9 9, g32p_row19_traceSegment_083_0288_0009, g32p_row19_traceSegment_083_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 306 9 9, g32p_row19_traceSegment_083_0306_0009, g32p_row19_traceSegment_083_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 288 18 18, g32p_row19_traceSegment_083_0288_0018, g32p_row19_traceSegment_083_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 324 9 9, g32p_row19_traceSegment_083_0324_0009, g32p_row19_traceSegment_083_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 342 9 9, g32p_row19_traceSegment_083_0342_0009, g32p_row19_traceSegment_083_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 324 18 18, g32p_row19_traceSegment_083_0324_0018, g32p_row19_traceSegment_083_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 288 36 36, g32p_row19_traceSegment_083_0288_0036, g32p_row19_traceSegment_083_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 360 9 9, g32p_row19_traceSegment_083_0360_0009, g32p_row19_traceSegment_083_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 378 9 9, g32p_row19_traceSegment_083_0378_0009, g32p_row19_traceSegment_083_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 360 18 18, g32p_row19_traceSegment_083_0360_0018, g32p_row19_traceSegment_083_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 396 9 9, g32p_row19_traceSegment_083_0396_0009, g32p_row19_traceSegment_083_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 414 9 9, g32p_row19_traceSegment_083_0414_0009, g32p_row19_traceSegment_083_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 396 18 18, g32p_row19_traceSegment_083_0396_0018, g32p_row19_traceSegment_083_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 360 36 36, g32p_row19_traceSegment_083_0360_0036, g32p_row19_traceSegment_083_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 288 72 72, g32p_row19_traceSegment_083_0288_0072, g32p_row19_traceSegment_083_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 432 9 9, g32p_row19_traceSegment_083_0432_0009, g32p_row19_traceSegment_083_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 450 9 9, g32p_row19_traceSegment_083_0450_0009, g32p_row19_traceSegment_083_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 432 18 18, g32p_row19_traceSegment_083_0432_0018, g32p_row19_traceSegment_083_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 468 9 9, g32p_row19_traceSegment_083_0468_0009, g32p_row19_traceSegment_083_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 486 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 486 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 486 9 9, g32p_row19_traceSegment_083_0486_0009, g32p_row19_traceSegment_083_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 468 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 468 18 18, g32p_row19_traceSegment_083_0468_0018, g32p_row19_traceSegment_083_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 432 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 432 36 36, g32p_row19_traceSegment_083_0432_0036, g32p_row19_traceSegment_083_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 504 9 9, g32p_row19_traceSegment_083_0504_0009, g32p_row19_traceSegment_083_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 522 9 9, g32p_row19_traceSegment_083_0522_0009, g32p_row19_traceSegment_083_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 504 18 18, g32p_row19_traceSegment_083_0504_0018, g32p_row19_traceSegment_083_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 540 9 9, g32p_row19_traceSegment_083_0540_0009, g32p_row19_traceSegment_083_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 558 9 9, g32p_row19_traceSegment_083_0558_0009, g32p_row19_traceSegment_083_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 540 18 18, g32p_row19_traceSegment_083_0540_0018, g32p_row19_traceSegment_083_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 504 36 36, g32p_row19_traceSegment_083_0504_0036, g32p_row19_traceSegment_083_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 432 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 432 72 72, g32p_row19_traceSegment_083_0432_0072, g32p_row19_traceSegment_083_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_083 288 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 288 144 144, g32p_row19_traceSegment_083_0288_0144, g32p_row19_traceSegment_083_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_083 0 576 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 288 288, g32p_row19_traceSegment_083_0000_0288, g32p_row19_traceSegment_083_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 576 9 9, g32p_row19_traceSegment_083_0576_0009, g32p_row19_traceSegment_083_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 594 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 594 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 594 9 9, g32p_row19_traceSegment_083_0594_0009, g32p_row19_traceSegment_083_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 576 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 576 18 18, g32p_row19_traceSegment_083_0576_0018, g32p_row19_traceSegment_083_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 612 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 612 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 612 9 9, g32p_row19_traceSegment_083_0612_0009, g32p_row19_traceSegment_083_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 630 9 9, g32p_row19_traceSegment_083_0630_0009, g32p_row19_traceSegment_083_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 612 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 612 18 18, g32p_row19_traceSegment_083_0612_0018, g32p_row19_traceSegment_083_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 576 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 576 36 36, g32p_row19_traceSegment_083_0576_0036, g32p_row19_traceSegment_083_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 648 9 9, g32p_row19_traceSegment_083_0648_0009, g32p_row19_traceSegment_083_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 666 9 9, g32p_row19_traceSegment_083_0666_0009, g32p_row19_traceSegment_083_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 648 18 18, g32p_row19_traceSegment_083_0648_0018, g32p_row19_traceSegment_083_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 684 9 9, g32p_row19_traceSegment_083_0684_0009, g32p_row19_traceSegment_083_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 702 9 9, g32p_row19_traceSegment_083_0702_0009, g32p_row19_traceSegment_083_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 684 18 18, g32p_row19_traceSegment_083_0684_0018, g32p_row19_traceSegment_083_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 648 36 36, g32p_row19_traceSegment_083_0648_0036, g32p_row19_traceSegment_083_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 576 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 576 72 72, g32p_row19_traceSegment_083_0576_0072, g32p_row19_traceSegment_083_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 720 9 9, g32p_row19_traceSegment_083_0720_0009, g32p_row19_traceSegment_083_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 738 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 747 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 738 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 738 9 9, g32p_row19_traceSegment_083_0738_0009, g32p_row19_traceSegment_083_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 720 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 720 18 18, g32p_row19_traceSegment_083_0720_0018, g32p_row19_traceSegment_083_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 756 9 9, g32p_row19_traceSegment_083_0756_0009, g32p_row19_traceSegment_083_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 774 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 783 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 774 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 774 9 9, g32p_row19_traceSegment_083_0774_0009, g32p_row19_traceSegment_083_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 756 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 756 18 18, g32p_row19_traceSegment_083_0756_0018, g32p_row19_traceSegment_083_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 720 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 720 36 36, g32p_row19_traceSegment_083_0720_0036, g32p_row19_traceSegment_083_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 792 9 9, g32p_row19_traceSegment_083_0792_0009, g32p_row19_traceSegment_083_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 810 9 9, g32p_row19_traceSegment_083_0810_0009, g32p_row19_traceSegment_083_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 792 18 18, g32p_row19_traceSegment_083_0792_0018, g32p_row19_traceSegment_083_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 828 9 9, g32p_row19_traceSegment_083_0828_0009, g32p_row19_traceSegment_083_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 846 9 9, g32p_row19_traceSegment_083_0846_0009, g32p_row19_traceSegment_083_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 828 18 18, g32p_row19_traceSegment_083_0828_0018, g32p_row19_traceSegment_083_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 792 36 36, g32p_row19_traceSegment_083_0792_0036, g32p_row19_traceSegment_083_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 720 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 720 72 72, g32p_row19_traceSegment_083_0720_0072, g32p_row19_traceSegment_083_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_083 576 288 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 576 144 144, g32p_row19_traceSegment_083_0576_0144, g32p_row19_traceSegment_083_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 864 9 9, g32p_row19_traceSegment_083_0864_0009, g32p_row19_traceSegment_083_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 882 9 9, g32p_row19_traceSegment_083_0882_0009, g32p_row19_traceSegment_083_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 864 18 18, g32p_row19_traceSegment_083_0864_0018, g32p_row19_traceSegment_083_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 900 9 9, g32p_row19_traceSegment_083_0900_0009, g32p_row19_traceSegment_083_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 918 9 9, g32p_row19_traceSegment_083_0918_0009, g32p_row19_traceSegment_083_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 900 18 18, g32p_row19_traceSegment_083_0900_0018, g32p_row19_traceSegment_083_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 864 36 36, g32p_row19_traceSegment_083_0864_0036, g32p_row19_traceSegment_083_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 936 9 9, g32p_row19_traceSegment_083_0936_0009, g32p_row19_traceSegment_083_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 954 9 9, g32p_row19_traceSegment_083_0954_0009, g32p_row19_traceSegment_083_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 936 18 18, g32p_row19_traceSegment_083_0936_0018, g32p_row19_traceSegment_083_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 972 9 9, g32p_row19_traceSegment_083_0972_0009, g32p_row19_traceSegment_083_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 990 9 9, g32p_row19_traceSegment_083_0990_0009, g32p_row19_traceSegment_083_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 972 18 18, g32p_row19_traceSegment_083_0972_0018, g32p_row19_traceSegment_083_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 936 36 36, g32p_row19_traceSegment_083_0936_0036, g32p_row19_traceSegment_083_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 864 72 72, g32p_row19_traceSegment_083_0864_0072, g32p_row19_traceSegment_083_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1008 9 9, g32p_row19_traceSegment_083_1008_0009, g32p_row19_traceSegment_083_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1026 9 9, g32p_row19_traceSegment_083_1026_0009, g32p_row19_traceSegment_083_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1008 18 18, g32p_row19_traceSegment_083_1008_0018, g32p_row19_traceSegment_083_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1044 9 9, g32p_row19_traceSegment_083_1044_0009, g32p_row19_traceSegment_083_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1062 9 9, g32p_row19_traceSegment_083_1062_0009, g32p_row19_traceSegment_083_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1044 18 18, g32p_row19_traceSegment_083_1044_0018, g32p_row19_traceSegment_083_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1008 36 36, g32p_row19_traceSegment_083_1008_0036, g32p_row19_traceSegment_083_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1080 9 9, g32p_row19_traceSegment_083_1080_0009, g32p_row19_traceSegment_083_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1098 9 9, g32p_row19_traceSegment_083_1098_0009, g32p_row19_traceSegment_083_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1080 18 18, g32p_row19_traceSegment_083_1080_0018, g32p_row19_traceSegment_083_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1116 9 9, g32p_row19_traceSegment_083_1116_0009, g32p_row19_traceSegment_083_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_083 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_083_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_083 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1134 9 9, g32p_row19_traceSegment_083_1134_0009, g32p_row19_traceSegment_083_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_083 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1116 18 18, g32p_row19_traceSegment_083_1116_0018, g32p_row19_traceSegment_083_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_083 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1080 36 36, g32p_row19_traceSegment_083_1080_0036, g32p_row19_traceSegment_083_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_083_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_083 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 1008 72 72, g32p_row19_traceSegment_083_1008_0072, g32p_row19_traceSegment_083_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_083 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 864 144 144, g32p_row19_traceSegment_083_0864_0144, g32p_row19_traceSegment_083_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_083 576 576 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 576 288 288, g32p_row19_traceSegment_083_0576_0288, g32p_row19_traceSegment_083_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_083_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_083 0 1152 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_083 0 576 576, g32p_row19_traceSegment_083_0000_0576, g32p_row19_traceSegment_083_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 83 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_083_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_090 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 90 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_090_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 9 9, g32p_row19_traceSegment_090_0000_0009, g32p_row19_traceSegment_090_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 18 9 9, g32p_row19_traceSegment_090_0018_0009, g32p_row19_traceSegment_090_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 18 18, g32p_row19_traceSegment_090_0000_0018, g32p_row19_traceSegment_090_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 36 9 9, g32p_row19_traceSegment_090_0036_0009, g32p_row19_traceSegment_090_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 54 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 63 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 54 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 54 9 9, g32p_row19_traceSegment_090_0054_0009, g32p_row19_traceSegment_090_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 36 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 36 18 18, g32p_row19_traceSegment_090_0036_0018, g32p_row19_traceSegment_090_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 0 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 36 36, g32p_row19_traceSegment_090_0000_0036, g32p_row19_traceSegment_090_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 72 9 9, g32p_row19_traceSegment_090_0072_0009, g32p_row19_traceSegment_090_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 90 9 9, g32p_row19_traceSegment_090_0090_0009, g32p_row19_traceSegment_090_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 72 18 18, g32p_row19_traceSegment_090_0072_0018, g32p_row19_traceSegment_090_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 108 9 9, g32p_row19_traceSegment_090_0108_0009, g32p_row19_traceSegment_090_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 135 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 126 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 126 9 9, g32p_row19_traceSegment_090_0126_0009, g32p_row19_traceSegment_090_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 108 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 108 18 18, g32p_row19_traceSegment_090_0108_0018, g32p_row19_traceSegment_090_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 72 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 72 36 36, g32p_row19_traceSegment_090_0072_0036, g32p_row19_traceSegment_090_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 0 144 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 72 72, g32p_row19_traceSegment_090_0000_0072, g32p_row19_traceSegment_090_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 144 9 9, g32p_row19_traceSegment_090_0144_0009, g32p_row19_traceSegment_090_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 162 9 9, g32p_row19_traceSegment_090_0162_0009, g32p_row19_traceSegment_090_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 144 18 18, g32p_row19_traceSegment_090_0144_0018, g32p_row19_traceSegment_090_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 180 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 180 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 180 9 9, g32p_row19_traceSegment_090_0180_0009, g32p_row19_traceSegment_090_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 198 9 9, g32p_row19_traceSegment_090_0198_0009, g32p_row19_traceSegment_090_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 180 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 180 18 18, g32p_row19_traceSegment_090_0180_0018, g32p_row19_traceSegment_090_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 144 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 144 36 36, g32p_row19_traceSegment_090_0144_0036, g32p_row19_traceSegment_090_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 216 9 9, g32p_row19_traceSegment_090_0216_0009, g32p_row19_traceSegment_090_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 234 9 9, g32p_row19_traceSegment_090_0234_0009, g32p_row19_traceSegment_090_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 216 18 18, g32p_row19_traceSegment_090_0216_0018, g32p_row19_traceSegment_090_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 252 9 9, g32p_row19_traceSegment_090_0252_0009, g32p_row19_traceSegment_090_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 270 9 9, g32p_row19_traceSegment_090_0270_0009, g32p_row19_traceSegment_090_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 252 18 18, g32p_row19_traceSegment_090_0252_0018, g32p_row19_traceSegment_090_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 216 36 36, g32p_row19_traceSegment_090_0216_0036, g32p_row19_traceSegment_090_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 144 72 72, g32p_row19_traceSegment_090_0144_0072, g32p_row19_traceSegment_090_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_090 0 288 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 144 144, g32p_row19_traceSegment_090_0000_0144, g32p_row19_traceSegment_090_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 288 9 9, g32p_row19_traceSegment_090_0288_0009, g32p_row19_traceSegment_090_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 306 9 9, g32p_row19_traceSegment_090_0306_0009, g32p_row19_traceSegment_090_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 288 18 18, g32p_row19_traceSegment_090_0288_0018, g32p_row19_traceSegment_090_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 324 9 9, g32p_row19_traceSegment_090_0324_0009, g32p_row19_traceSegment_090_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 342 9 9, g32p_row19_traceSegment_090_0342_0009, g32p_row19_traceSegment_090_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 324 18 18, g32p_row19_traceSegment_090_0324_0018, g32p_row19_traceSegment_090_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 288 36 36, g32p_row19_traceSegment_090_0288_0036, g32p_row19_traceSegment_090_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 360 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 360 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 360 9 9, g32p_row19_traceSegment_090_0360_0009, g32p_row19_traceSegment_090_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 378 9 9, g32p_row19_traceSegment_090_0378_0009, g32p_row19_traceSegment_090_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 360 18 18, g32p_row19_traceSegment_090_0360_0018, g32p_row19_traceSegment_090_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 396 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 396 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 396 9 9, g32p_row19_traceSegment_090_0396_0009, g32p_row19_traceSegment_090_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 414 9 9, g32p_row19_traceSegment_090_0414_0009, g32p_row19_traceSegment_090_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 396 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 396 18 18, g32p_row19_traceSegment_090_0396_0018, g32p_row19_traceSegment_090_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 360 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 360 36 36, g32p_row19_traceSegment_090_0360_0036, g32p_row19_traceSegment_090_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 288 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 288 72 72, g32p_row19_traceSegment_090_0288_0072, g32p_row19_traceSegment_090_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 432 9 9, g32p_row19_traceSegment_090_0432_0009, g32p_row19_traceSegment_090_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 450 9 9, g32p_row19_traceSegment_090_0450_0009, g32p_row19_traceSegment_090_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 432 18 18, g32p_row19_traceSegment_090_0432_0018, g32p_row19_traceSegment_090_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 468 9 9, g32p_row19_traceSegment_090_0468_0009, g32p_row19_traceSegment_090_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 486 9 9, g32p_row19_traceSegment_090_0486_0009, g32p_row19_traceSegment_090_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 468 18 18, g32p_row19_traceSegment_090_0468_0018, g32p_row19_traceSegment_090_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 432 36 36, g32p_row19_traceSegment_090_0432_0036, g32p_row19_traceSegment_090_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 504 9 9, g32p_row19_traceSegment_090_0504_0009, g32p_row19_traceSegment_090_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 522 9 9, g32p_row19_traceSegment_090_0522_0009, g32p_row19_traceSegment_090_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 504 18 18, g32p_row19_traceSegment_090_0504_0018, g32p_row19_traceSegment_090_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 540 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 540 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 540 9 9, g32p_row19_traceSegment_090_0540_0009, g32p_row19_traceSegment_090_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 558 9 9, g32p_row19_traceSegment_090_0558_0009, g32p_row19_traceSegment_090_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 540 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 540 18 18, g32p_row19_traceSegment_090_0540_0018, g32p_row19_traceSegment_090_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 504 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 504 36 36, g32p_row19_traceSegment_090_0504_0036, g32p_row19_traceSegment_090_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 432 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 432 72 72, g32p_row19_traceSegment_090_0432_0072, g32p_row19_traceSegment_090_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_090 288 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 288 144 144, g32p_row19_traceSegment_090_0288_0144, g32p_row19_traceSegment_090_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_090 0 576 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 288 288, g32p_row19_traceSegment_090_0000_0288, g32p_row19_traceSegment_090_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 576 9 9, g32p_row19_traceSegment_090_0576_0009, g32p_row19_traceSegment_090_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 594 9 9, g32p_row19_traceSegment_090_0594_0009, g32p_row19_traceSegment_090_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 576 18 18, g32p_row19_traceSegment_090_0576_0018, g32p_row19_traceSegment_090_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 612 9 9, g32p_row19_traceSegment_090_0612_0009, g32p_row19_traceSegment_090_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 630 9 9, g32p_row19_traceSegment_090_0630_0009, g32p_row19_traceSegment_090_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 612 18 18, g32p_row19_traceSegment_090_0612_0018, g32p_row19_traceSegment_090_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 576 36 36, g32p_row19_traceSegment_090_0576_0036, g32p_row19_traceSegment_090_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 648 9 9, g32p_row19_traceSegment_090_0648_0009, g32p_row19_traceSegment_090_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 666 9 9, g32p_row19_traceSegment_090_0666_0009, g32p_row19_traceSegment_090_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 648 18 18, g32p_row19_traceSegment_090_0648_0018, g32p_row19_traceSegment_090_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 684 9 9, g32p_row19_traceSegment_090_0684_0009, g32p_row19_traceSegment_090_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 702 9 9, g32p_row19_traceSegment_090_0702_0009, g32p_row19_traceSegment_090_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 684 18 18, g32p_row19_traceSegment_090_0684_0018, g32p_row19_traceSegment_090_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 648 36 36, g32p_row19_traceSegment_090_0648_0036, g32p_row19_traceSegment_090_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 576 72 72, g32p_row19_traceSegment_090_0576_0072, g32p_row19_traceSegment_090_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 720 9 9, g32p_row19_traceSegment_090_0720_0009, g32p_row19_traceSegment_090_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 738 9 9, g32p_row19_traceSegment_090_0738_0009, g32p_row19_traceSegment_090_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 720 18 18, g32p_row19_traceSegment_090_0720_0018, g32p_row19_traceSegment_090_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 756 9 9, g32p_row19_traceSegment_090_0756_0009, g32p_row19_traceSegment_090_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 774 9 9, g32p_row19_traceSegment_090_0774_0009, g32p_row19_traceSegment_090_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 756 18 18, g32p_row19_traceSegment_090_0756_0018, g32p_row19_traceSegment_090_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 720 36 36, g32p_row19_traceSegment_090_0720_0036, g32p_row19_traceSegment_090_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 792 9 9, g32p_row19_traceSegment_090_0792_0009, g32p_row19_traceSegment_090_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 810 9 9, g32p_row19_traceSegment_090_0810_0009, g32p_row19_traceSegment_090_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 792 18 18, g32p_row19_traceSegment_090_0792_0018, g32p_row19_traceSegment_090_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 828 9 9, g32p_row19_traceSegment_090_0828_0009, g32p_row19_traceSegment_090_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 846 9 9, g32p_row19_traceSegment_090_0846_0009, g32p_row19_traceSegment_090_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 828 18 18, g32p_row19_traceSegment_090_0828_0018, g32p_row19_traceSegment_090_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 792 36 36, g32p_row19_traceSegment_090_0792_0036, g32p_row19_traceSegment_090_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 720 72 72, g32p_row19_traceSegment_090_0720_0072, g32p_row19_traceSegment_090_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_090 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 576 144 144, g32p_row19_traceSegment_090_0576_0144, g32p_row19_traceSegment_090_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 864 9 9, g32p_row19_traceSegment_090_0864_0009, g32p_row19_traceSegment_090_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 882 9 9, g32p_row19_traceSegment_090_0882_0009, g32p_row19_traceSegment_090_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 864 18 18, g32p_row19_traceSegment_090_0864_0018, g32p_row19_traceSegment_090_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 900 9 9, g32p_row19_traceSegment_090_0900_0009, g32p_row19_traceSegment_090_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 918 9 9, g32p_row19_traceSegment_090_0918_0009, g32p_row19_traceSegment_090_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 900 18 18, g32p_row19_traceSegment_090_0900_0018, g32p_row19_traceSegment_090_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 864 36 36, g32p_row19_traceSegment_090_0864_0036, g32p_row19_traceSegment_090_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 936 9 9, g32p_row19_traceSegment_090_0936_0009, g32p_row19_traceSegment_090_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 954 9 9, g32p_row19_traceSegment_090_0954_0009, g32p_row19_traceSegment_090_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 936 18 18, g32p_row19_traceSegment_090_0936_0018, g32p_row19_traceSegment_090_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 972 9 9, g32p_row19_traceSegment_090_0972_0009, g32p_row19_traceSegment_090_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 990 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 999 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 990 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 990 9 9, g32p_row19_traceSegment_090_0990_0009, g32p_row19_traceSegment_090_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 972 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 972 18 18, g32p_row19_traceSegment_090_0972_0018, g32p_row19_traceSegment_090_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 936 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 936 36 36, g32p_row19_traceSegment_090_0936_0036, g32p_row19_traceSegment_090_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 864 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 864 72 72, g32p_row19_traceSegment_090_0864_0072, g32p_row19_traceSegment_090_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1008 9 9, g32p_row19_traceSegment_090_1008_0009, g32p_row19_traceSegment_090_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1026 9 9, g32p_row19_traceSegment_090_1026_0009, g32p_row19_traceSegment_090_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1008 18 18, g32p_row19_traceSegment_090_1008_0018, g32p_row19_traceSegment_090_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1044 9 9, g32p_row19_traceSegment_090_1044_0009, g32p_row19_traceSegment_090_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1062 9 9, g32p_row19_traceSegment_090_1062_0009, g32p_row19_traceSegment_090_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1044 18 18, g32p_row19_traceSegment_090_1044_0018, g32p_row19_traceSegment_090_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1008 36 36, g32p_row19_traceSegment_090_1008_0036, g32p_row19_traceSegment_090_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1080 9 9, g32p_row19_traceSegment_090_1080_0009, g32p_row19_traceSegment_090_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1098 9 9, g32p_row19_traceSegment_090_1098_0009, g32p_row19_traceSegment_090_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1080 18 18, g32p_row19_traceSegment_090_1080_0018, g32p_row19_traceSegment_090_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1116 9 9, g32p_row19_traceSegment_090_1116_0009, g32p_row19_traceSegment_090_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_090 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_090_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_090 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1134 9 9, g32p_row19_traceSegment_090_1134_0009, g32p_row19_traceSegment_090_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_090 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1116 18 18, g32p_row19_traceSegment_090_1116_0018, g32p_row19_traceSegment_090_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_090 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1080 36 36, g32p_row19_traceSegment_090_1080_0036, g32p_row19_traceSegment_090_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_090_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_090 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 1008 72 72, g32p_row19_traceSegment_090_1008_0072, g32p_row19_traceSegment_090_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_090 864 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 864 144 144, g32p_row19_traceSegment_090_0864_0144, g32p_row19_traceSegment_090_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_090 576 576 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 576 288 288, g32p_row19_traceSegment_090_0576_0288, g32p_row19_traceSegment_090_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_090_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_090 0 1152 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_090 0 576 576, g32p_row19_traceSegment_090_0000_0576, g32p_row19_traceSegment_090_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 90 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_090_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_092_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 9 9, g32p_row19_traceSegment_092_0000_0009, g32p_row19_traceSegment_092_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 18 9 9, g32p_row19_traceSegment_092_0018_0009, g32p_row19_traceSegment_092_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 18 18, g32p_row19_traceSegment_092_0000_0018, g32p_row19_traceSegment_092_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 36 9 9, g32p_row19_traceSegment_092_0036_0009, g32p_row19_traceSegment_092_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 54 9 9, g32p_row19_traceSegment_092_0054_0009, g32p_row19_traceSegment_092_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 36 18 18, g32p_row19_traceSegment_092_0036_0018, g32p_row19_traceSegment_092_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 36 36, g32p_row19_traceSegment_092_0000_0036, g32p_row19_traceSegment_092_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 72 9 9, g32p_row19_traceSegment_092_0072_0009, g32p_row19_traceSegment_092_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 90 9 9, g32p_row19_traceSegment_092_0090_0009, g32p_row19_traceSegment_092_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 72 18 18, g32p_row19_traceSegment_092_0072_0018, g32p_row19_traceSegment_092_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 117 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 108 9 9, g32p_row19_traceSegment_092_0108_0009, g32p_row19_traceSegment_092_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 135 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 126 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 126 9 9, g32p_row19_traceSegment_092_0126_0009, g32p_row19_traceSegment_092_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 108 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 108 18 18, g32p_row19_traceSegment_092_0108_0018, g32p_row19_traceSegment_092_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 72 36 36, g32p_row19_traceSegment_092_0072_0036, g32p_row19_traceSegment_092_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 0 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 72 72, g32p_row19_traceSegment_092_0000_0072, g32p_row19_traceSegment_092_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 144 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 144 9 9, g32p_row19_traceSegment_092_0144_0009, g32p_row19_traceSegment_092_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 162 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 171 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 162 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 162 9 9, g32p_row19_traceSegment_092_0162_0009, g32p_row19_traceSegment_092_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 144 36 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 144 18 18, g32p_row19_traceSegment_092_0144_0018, g32p_row19_traceSegment_092_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 180 9 9, g32p_row19_traceSegment_092_0180_0009, g32p_row19_traceSegment_092_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 198 9 9, g32p_row19_traceSegment_092_0198_0009, g32p_row19_traceSegment_092_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 180 18 18, g32p_row19_traceSegment_092_0180_0018, g32p_row19_traceSegment_092_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 144 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 144 36 36, g32p_row19_traceSegment_092_0144_0036, g32p_row19_traceSegment_092_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 216 9 9, g32p_row19_traceSegment_092_0216_0009, g32p_row19_traceSegment_092_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 234 9 9, g32p_row19_traceSegment_092_0234_0009, g32p_row19_traceSegment_092_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 216 18 18, g32p_row19_traceSegment_092_0216_0018, g32p_row19_traceSegment_092_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 252 9 9, g32p_row19_traceSegment_092_0252_0009, g32p_row19_traceSegment_092_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 270 9 9, g32p_row19_traceSegment_092_0270_0009, g32p_row19_traceSegment_092_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 252 18 18, g32p_row19_traceSegment_092_0252_0018, g32p_row19_traceSegment_092_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 216 36 36, g32p_row19_traceSegment_092_0216_0036, g32p_row19_traceSegment_092_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 144 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 144 72 72, g32p_row19_traceSegment_092_0144_0072, g32p_row19_traceSegment_092_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_092 0 288 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 144 144, g32p_row19_traceSegment_092_0000_0144, g32p_row19_traceSegment_092_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 297 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 288 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 288 9 9, g32p_row19_traceSegment_092_0288_0009, g32p_row19_traceSegment_092_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 306 9 9, g32p_row19_traceSegment_092_0306_0009, g32p_row19_traceSegment_092_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 288 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 288 18 18, g32p_row19_traceSegment_092_0288_0018, g32p_row19_traceSegment_092_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 324 9 9, g32p_row19_traceSegment_092_0324_0009, g32p_row19_traceSegment_092_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 342 9 9, g32p_row19_traceSegment_092_0342_0009, g32p_row19_traceSegment_092_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 324 18 18, g32p_row19_traceSegment_092_0324_0018, g32p_row19_traceSegment_092_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 288 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 288 36 36, g32p_row19_traceSegment_092_0288_0036, g32p_row19_traceSegment_092_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 360 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 369 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 360 18 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 360 9 9, g32p_row19_traceSegment_092_0360_0009, g32p_row19_traceSegment_092_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 378 9 9, g32p_row19_traceSegment_092_0378_0009, g32p_row19_traceSegment_092_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 360 36 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 360 18 18, g32p_row19_traceSegment_092_0360_0018, g32p_row19_traceSegment_092_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 396 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 396 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 396 9 9, g32p_row19_traceSegment_092_0396_0009, g32p_row19_traceSegment_092_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 414 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 414 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 414 9 9, g32p_row19_traceSegment_092_0414_0009, g32p_row19_traceSegment_092_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 396 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 396 18 18, g32p_row19_traceSegment_092_0396_0018, g32p_row19_traceSegment_092_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 360 72 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 360 36 36, g32p_row19_traceSegment_092_0360_0036, g32p_row19_traceSegment_092_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 288 144 = [4, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 288 72 72, g32p_row19_traceSegment_092_0288_0072, g32p_row19_traceSegment_092_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 432 9 9, g32p_row19_traceSegment_092_0432_0009, g32p_row19_traceSegment_092_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 450 9 9, g32p_row19_traceSegment_092_0450_0009, g32p_row19_traceSegment_092_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 432 18 18, g32p_row19_traceSegment_092_0432_0018, g32p_row19_traceSegment_092_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 468 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 468 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 468 9 9, g32p_row19_traceSegment_092_0468_0009, g32p_row19_traceSegment_092_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 486 9 9, g32p_row19_traceSegment_092_0486_0009, g32p_row19_traceSegment_092_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 468 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 468 18 18, g32p_row19_traceSegment_092_0468_0018, g32p_row19_traceSegment_092_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 432 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 432 36 36, g32p_row19_traceSegment_092_0432_0036, g32p_row19_traceSegment_092_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 504 9 9, g32p_row19_traceSegment_092_0504_0009, g32p_row19_traceSegment_092_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 522 9 9, g32p_row19_traceSegment_092_0522_0009, g32p_row19_traceSegment_092_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 504 18 18, g32p_row19_traceSegment_092_0504_0018, g32p_row19_traceSegment_092_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 540 9 9, g32p_row19_traceSegment_092_0540_0009, g32p_row19_traceSegment_092_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 558 9 9, g32p_row19_traceSegment_092_0558_0009, g32p_row19_traceSegment_092_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 540 18 18, g32p_row19_traceSegment_092_0540_0018, g32p_row19_traceSegment_092_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 504 36 36, g32p_row19_traceSegment_092_0504_0036, g32p_row19_traceSegment_092_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 432 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 432 72 72, g32p_row19_traceSegment_092_0432_0072, g32p_row19_traceSegment_092_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_092 288 288 = [5, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 288 144 144, g32p_row19_traceSegment_092_0288_0144, g32p_row19_traceSegment_092_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_092 0 576 = [5, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 288 288, g32p_row19_traceSegment_092_0000_0288, g32p_row19_traceSegment_092_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 576 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 576 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 576 9 9, g32p_row19_traceSegment_092_0576_0009, g32p_row19_traceSegment_092_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 594 9 9, g32p_row19_traceSegment_092_0594_0009, g32p_row19_traceSegment_092_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 576 18 18, g32p_row19_traceSegment_092_0576_0018, g32p_row19_traceSegment_092_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 612 9 9, g32p_row19_traceSegment_092_0612_0009, g32p_row19_traceSegment_092_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 630 9 9, g32p_row19_traceSegment_092_0630_0009, g32p_row19_traceSegment_092_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 612 18 18, g32p_row19_traceSegment_092_0612_0018, g32p_row19_traceSegment_092_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 576 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 576 36 36, g32p_row19_traceSegment_092_0576_0036, g32p_row19_traceSegment_092_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 648 9 9, g32p_row19_traceSegment_092_0648_0009, g32p_row19_traceSegment_092_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 666 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 666 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 666 9 9, g32p_row19_traceSegment_092_0666_0009, g32p_row19_traceSegment_092_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 648 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 648 18 18, g32p_row19_traceSegment_092_0648_0018, g32p_row19_traceSegment_092_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 684 9 9, g32p_row19_traceSegment_092_0684_0009, g32p_row19_traceSegment_092_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 702 9 9, g32p_row19_traceSegment_092_0702_0009, g32p_row19_traceSegment_092_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 684 18 18, g32p_row19_traceSegment_092_0684_0018, g32p_row19_traceSegment_092_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 648 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 648 36 36, g32p_row19_traceSegment_092_0648_0036, g32p_row19_traceSegment_092_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 576 144 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 576 72 72, g32p_row19_traceSegment_092_0576_0072, g32p_row19_traceSegment_092_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 729 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 720 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 720 9 9, g32p_row19_traceSegment_092_0720_0009, g32p_row19_traceSegment_092_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 738 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 738 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 738 9 9, g32p_row19_traceSegment_092_0738_0009, g32p_row19_traceSegment_092_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 720 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 720 18 18, g32p_row19_traceSegment_092_0720_0018, g32p_row19_traceSegment_092_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 756 9 9, g32p_row19_traceSegment_092_0756_0009, g32p_row19_traceSegment_092_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 774 9 9, g32p_row19_traceSegment_092_0774_0009, g32p_row19_traceSegment_092_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 756 18 18, g32p_row19_traceSegment_092_0756_0018, g32p_row19_traceSegment_092_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 720 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 720 36 36, g32p_row19_traceSegment_092_0720_0036, g32p_row19_traceSegment_092_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 792 9 9, g32p_row19_traceSegment_092_0792_0009, g32p_row19_traceSegment_092_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 810 9 9, g32p_row19_traceSegment_092_0810_0009, g32p_row19_traceSegment_092_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 792 18 18, g32p_row19_traceSegment_092_0792_0018, g32p_row19_traceSegment_092_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 828 9 9, g32p_row19_traceSegment_092_0828_0009, g32p_row19_traceSegment_092_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 846 9 9, g32p_row19_traceSegment_092_0846_0009, g32p_row19_traceSegment_092_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 828 18 18, g32p_row19_traceSegment_092_0828_0018, g32p_row19_traceSegment_092_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 792 36 36, g32p_row19_traceSegment_092_0792_0036, g32p_row19_traceSegment_092_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 720 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 720 72 72, g32p_row19_traceSegment_092_0720_0072, g32p_row19_traceSegment_092_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_092 576 288 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 576 144 144, g32p_row19_traceSegment_092_0576_0144, g32p_row19_traceSegment_092_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 864 9 9, g32p_row19_traceSegment_092_0864_0009, g32p_row19_traceSegment_092_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 882 9 9, g32p_row19_traceSegment_092_0882_0009, g32p_row19_traceSegment_092_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 864 18 18, g32p_row19_traceSegment_092_0864_0018, g32p_row19_traceSegment_092_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 909 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 900 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 900 9 9, g32p_row19_traceSegment_092_0900_0009, g32p_row19_traceSegment_092_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 918 9 = [2, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 927 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 918 18 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 918 9 9, g32p_row19_traceSegment_092_0918_0009, g32p_row19_traceSegment_092_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 900 36 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 900 18 18, g32p_row19_traceSegment_092_0900_0018, g32p_row19_traceSegment_092_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 864 72 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 864 36 36, g32p_row19_traceSegment_092_0864_0036, g32p_row19_traceSegment_092_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 936 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 945 9 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 936 18 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 936 9 9, g32p_row19_traceSegment_092_0936_0009, g32p_row19_traceSegment_092_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 954 9 9, g32p_row19_traceSegment_092_0954_0009, g32p_row19_traceSegment_092_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 936 36 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 936 18 18, g32p_row19_traceSegment_092_0936_0018, g32p_row19_traceSegment_092_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 972 9 9, g32p_row19_traceSegment_092_0972_0009, g32p_row19_traceSegment_092_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 999 9 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 990 18 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 990 9 9, g32p_row19_traceSegment_092_0990_0009, g32p_row19_traceSegment_092_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 972 36 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 972 18 18, g32p_row19_traceSegment_092_0972_0018, g32p_row19_traceSegment_092_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 936 72 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 936 36 36, g32p_row19_traceSegment_092_0936_0036, g32p_row19_traceSegment_092_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 864 144 = [6, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 864 72 72, g32p_row19_traceSegment_092_0864_0072, g32p_row19_traceSegment_092_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1008 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1017 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1008 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1008 9 9, g32p_row19_traceSegment_092_1008_0009, g32p_row19_traceSegment_092_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1026 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1026 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1026 9 9, g32p_row19_traceSegment_092_1026_0009, g32p_row19_traceSegment_092_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 1008 36 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1008 18 18, g32p_row19_traceSegment_092_1008_0018, g32p_row19_traceSegment_092_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1044 9 9, g32p_row19_traceSegment_092_1044_0009, g32p_row19_traceSegment_092_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1062 9 9, g32p_row19_traceSegment_092_1062_0009, g32p_row19_traceSegment_092_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1044 18 18, g32p_row19_traceSegment_092_1044_0018, g32p_row19_traceSegment_092_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 1008 72 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1008 36 36, g32p_row19_traceSegment_092_1008_0036, g32p_row19_traceSegment_092_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1080 9 9, g32p_row19_traceSegment_092_1080_0009, g32p_row19_traceSegment_092_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1098 9 9, g32p_row19_traceSegment_092_1098_0009, g32p_row19_traceSegment_092_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1080 18 18, g32p_row19_traceSegment_092_1080_0018, g32p_row19_traceSegment_092_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1116 9 9, g32p_row19_traceSegment_092_1116_0009, g32p_row19_traceSegment_092_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_092 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_092_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_092 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1134 9 9, g32p_row19_traceSegment_092_1134_0009, g32p_row19_traceSegment_092_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_092 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1116 18 18, g32p_row19_traceSegment_092_1116_0018, g32p_row19_traceSegment_092_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_092 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1080 36 36, g32p_row19_traceSegment_092_1080_0036, g32p_row19_traceSegment_092_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_092_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_092 1008 144 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 1008 72 72, g32p_row19_traceSegment_092_1008_0072, g32p_row19_traceSegment_092_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_092 864 288 = [8, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 864 144 144, g32p_row19_traceSegment_092_0864_0144, g32p_row19_traceSegment_092_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_092 576 576 = [11, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 576 288 288, g32p_row19_traceSegment_092_0576_0288, g32p_row19_traceSegment_092_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_092_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_092 0 1152 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_092 0 576 576, g32p_row19_traceSegment_092_0000_0576, g32p_row19_traceSegment_092_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 92 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_092_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_094 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 94 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_094_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 9 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 9 9, g32p_row19_traceSegment_094_0000_0009, g32p_row19_traceSegment_094_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 18 9 9, g32p_row19_traceSegment_094_0018_0009, g32p_row19_traceSegment_094_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 18 18, g32p_row19_traceSegment_094_0000_0018, g32p_row19_traceSegment_094_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 36 9 9, g32p_row19_traceSegment_094_0036_0009, g32p_row19_traceSegment_094_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 54 9 9, g32p_row19_traceSegment_094_0054_0009, g32p_row19_traceSegment_094_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 36 18 18, g32p_row19_traceSegment_094_0036_0018, g32p_row19_traceSegment_094_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 36 36, g32p_row19_traceSegment_094_0000_0036, g32p_row19_traceSegment_094_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 72 9 9, g32p_row19_traceSegment_094_0072_0009, g32p_row19_traceSegment_094_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 90 9 9, g32p_row19_traceSegment_094_0090_0009, g32p_row19_traceSegment_094_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 72 18 18, g32p_row19_traceSegment_094_0072_0018, g32p_row19_traceSegment_094_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 117 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 108 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 108 9 9, g32p_row19_traceSegment_094_0108_0009, g32p_row19_traceSegment_094_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 126 9 9, g32p_row19_traceSegment_094_0126_0009, g32p_row19_traceSegment_094_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 108 18 18, g32p_row19_traceSegment_094_0108_0018, g32p_row19_traceSegment_094_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 72 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 72 36 36, g32p_row19_traceSegment_094_0072_0036, g32p_row19_traceSegment_094_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 72 72, g32p_row19_traceSegment_094_0000_0072, g32p_row19_traceSegment_094_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 144 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 144 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 144 9 9, g32p_row19_traceSegment_094_0144_0009, g32p_row19_traceSegment_094_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 162 9 9, g32p_row19_traceSegment_094_0162_0009, g32p_row19_traceSegment_094_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 144 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 144 18 18, g32p_row19_traceSegment_094_0144_0018, g32p_row19_traceSegment_094_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 180 9 9, g32p_row19_traceSegment_094_0180_0009, g32p_row19_traceSegment_094_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 198 9 9, g32p_row19_traceSegment_094_0198_0009, g32p_row19_traceSegment_094_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 180 18 18, g32p_row19_traceSegment_094_0180_0018, g32p_row19_traceSegment_094_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 144 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 144 36 36, g32p_row19_traceSegment_094_0144_0036, g32p_row19_traceSegment_094_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 216 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 216 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 216 9 9, g32p_row19_traceSegment_094_0216_0009, g32p_row19_traceSegment_094_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 234 9 9, g32p_row19_traceSegment_094_0234_0009, g32p_row19_traceSegment_094_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 216 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 216 18 18, g32p_row19_traceSegment_094_0216_0018, g32p_row19_traceSegment_094_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 261 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 252 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 252 9 9, g32p_row19_traceSegment_094_0252_0009, g32p_row19_traceSegment_094_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 270 9 9, g32p_row19_traceSegment_094_0270_0009, g32p_row19_traceSegment_094_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 252 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 252 18 18, g32p_row19_traceSegment_094_0252_0018, g32p_row19_traceSegment_094_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 216 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 216 36 36, g32p_row19_traceSegment_094_0216_0036, g32p_row19_traceSegment_094_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 144 144 = [5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 144 72 72, g32p_row19_traceSegment_094_0144_0072, g32p_row19_traceSegment_094_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_094 0 288 = [7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 144 144, g32p_row19_traceSegment_094_0000_0144, g32p_row19_traceSegment_094_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 288 9 9, g32p_row19_traceSegment_094_0288_0009, g32p_row19_traceSegment_094_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 306 9 9, g32p_row19_traceSegment_094_0306_0009, g32p_row19_traceSegment_094_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 288 18 18, g32p_row19_traceSegment_094_0288_0018, g32p_row19_traceSegment_094_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 324 9 9, g32p_row19_traceSegment_094_0324_0009, g32p_row19_traceSegment_094_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 342 9 9, g32p_row19_traceSegment_094_0342_0009, g32p_row19_traceSegment_094_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 324 18 18, g32p_row19_traceSegment_094_0324_0018, g32p_row19_traceSegment_094_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 288 36 36, g32p_row19_traceSegment_094_0288_0036, g32p_row19_traceSegment_094_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 360 9 9, g32p_row19_traceSegment_094_0360_0009, g32p_row19_traceSegment_094_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 378 9 9, g32p_row19_traceSegment_094_0378_0009, g32p_row19_traceSegment_094_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 360 18 18, g32p_row19_traceSegment_094_0360_0018, g32p_row19_traceSegment_094_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 396 9 9, g32p_row19_traceSegment_094_0396_0009, g32p_row19_traceSegment_094_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 414 9 9, g32p_row19_traceSegment_094_0414_0009, g32p_row19_traceSegment_094_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 396 18 18, g32p_row19_traceSegment_094_0396_0018, g32p_row19_traceSegment_094_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 360 36 36, g32p_row19_traceSegment_094_0360_0036, g32p_row19_traceSegment_094_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 288 72 72, g32p_row19_traceSegment_094_0288_0072, g32p_row19_traceSegment_094_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 432 9 9, g32p_row19_traceSegment_094_0432_0009, g32p_row19_traceSegment_094_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 450 9 9, g32p_row19_traceSegment_094_0450_0009, g32p_row19_traceSegment_094_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 432 18 18, g32p_row19_traceSegment_094_0432_0018, g32p_row19_traceSegment_094_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 468 9 9, g32p_row19_traceSegment_094_0468_0009, g32p_row19_traceSegment_094_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 486 9 9, g32p_row19_traceSegment_094_0486_0009, g32p_row19_traceSegment_094_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 468 18 18, g32p_row19_traceSegment_094_0468_0018, g32p_row19_traceSegment_094_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 432 36 36, g32p_row19_traceSegment_094_0432_0036, g32p_row19_traceSegment_094_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 504 9 9, g32p_row19_traceSegment_094_0504_0009, g32p_row19_traceSegment_094_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 522 9 9, g32p_row19_traceSegment_094_0522_0009, g32p_row19_traceSegment_094_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 504 18 18, g32p_row19_traceSegment_094_0504_0018, g32p_row19_traceSegment_094_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 540 9 9, g32p_row19_traceSegment_094_0540_0009, g32p_row19_traceSegment_094_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 558 9 9, g32p_row19_traceSegment_094_0558_0009, g32p_row19_traceSegment_094_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 540 18 18, g32p_row19_traceSegment_094_0540_0018, g32p_row19_traceSegment_094_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 504 36 36, g32p_row19_traceSegment_094_0504_0036, g32p_row19_traceSegment_094_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 432 72 72, g32p_row19_traceSegment_094_0432_0072, g32p_row19_traceSegment_094_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_094 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 288 144 144, g32p_row19_traceSegment_094_0288_0144, g32p_row19_traceSegment_094_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_094 0 576 = [7] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 288 288, g32p_row19_traceSegment_094_0000_0288, g32p_row19_traceSegment_094_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 576 9 9, g32p_row19_traceSegment_094_0576_0009, g32p_row19_traceSegment_094_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 594 9 9, g32p_row19_traceSegment_094_0594_0009, g32p_row19_traceSegment_094_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 576 18 18, g32p_row19_traceSegment_094_0576_0018, g32p_row19_traceSegment_094_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 612 9 9, g32p_row19_traceSegment_094_0612_0009, g32p_row19_traceSegment_094_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 630 9 9, g32p_row19_traceSegment_094_0630_0009, g32p_row19_traceSegment_094_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 612 18 18, g32p_row19_traceSegment_094_0612_0018, g32p_row19_traceSegment_094_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 576 36 36, g32p_row19_traceSegment_094_0576_0036, g32p_row19_traceSegment_094_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 648 9 9, g32p_row19_traceSegment_094_0648_0009, g32p_row19_traceSegment_094_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 666 9 9, g32p_row19_traceSegment_094_0666_0009, g32p_row19_traceSegment_094_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 648 18 18, g32p_row19_traceSegment_094_0648_0018, g32p_row19_traceSegment_094_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 684 9 9, g32p_row19_traceSegment_094_0684_0009, g32p_row19_traceSegment_094_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 702 9 9, g32p_row19_traceSegment_094_0702_0009, g32p_row19_traceSegment_094_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 684 18 18, g32p_row19_traceSegment_094_0684_0018, g32p_row19_traceSegment_094_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 648 36 36, g32p_row19_traceSegment_094_0648_0036, g32p_row19_traceSegment_094_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 576 72 72, g32p_row19_traceSegment_094_0576_0072, g32p_row19_traceSegment_094_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 720 9 9, g32p_row19_traceSegment_094_0720_0009, g32p_row19_traceSegment_094_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 738 9 9, g32p_row19_traceSegment_094_0738_0009, g32p_row19_traceSegment_094_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 720 18 18, g32p_row19_traceSegment_094_0720_0018, g32p_row19_traceSegment_094_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 756 9 9, g32p_row19_traceSegment_094_0756_0009, g32p_row19_traceSegment_094_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 774 9 = [2] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 774 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 774 9 9, g32p_row19_traceSegment_094_0774_0009, g32p_row19_traceSegment_094_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 756 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 756 18 18, g32p_row19_traceSegment_094_0756_0018, g32p_row19_traceSegment_094_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 720 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 720 36 36, g32p_row19_traceSegment_094_0720_0036, g32p_row19_traceSegment_094_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 792 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 801 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 792 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 792 9 9, g32p_row19_traceSegment_094_0792_0009, g32p_row19_traceSegment_094_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 810 9 9, g32p_row19_traceSegment_094_0810_0009, g32p_row19_traceSegment_094_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 792 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 792 18 18, g32p_row19_traceSegment_094_0792_0018, g32p_row19_traceSegment_094_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 828 9 9, g32p_row19_traceSegment_094_0828_0009, g32p_row19_traceSegment_094_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 846 9 9, g32p_row19_traceSegment_094_0846_0009, g32p_row19_traceSegment_094_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 828 18 18, g32p_row19_traceSegment_094_0828_0018, g32p_row19_traceSegment_094_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 792 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 792 36 36, g32p_row19_traceSegment_094_0792_0036, g32p_row19_traceSegment_094_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 720 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 720 72 72, g32p_row19_traceSegment_094_0720_0072, g32p_row19_traceSegment_094_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_094 576 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 576 144 144, g32p_row19_traceSegment_094_0576_0144, g32p_row19_traceSegment_094_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 864 9 9, g32p_row19_traceSegment_094_0864_0009, g32p_row19_traceSegment_094_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 882 9 9, g32p_row19_traceSegment_094_0882_0009, g32p_row19_traceSegment_094_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 864 18 18, g32p_row19_traceSegment_094_0864_0018, g32p_row19_traceSegment_094_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 900 9 9, g32p_row19_traceSegment_094_0900_0009, g32p_row19_traceSegment_094_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 918 9 9, g32p_row19_traceSegment_094_0918_0009, g32p_row19_traceSegment_094_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 900 18 18, g32p_row19_traceSegment_094_0900_0018, g32p_row19_traceSegment_094_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 864 36 36, g32p_row19_traceSegment_094_0864_0036, g32p_row19_traceSegment_094_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 936 9 9, g32p_row19_traceSegment_094_0936_0009, g32p_row19_traceSegment_094_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 954 9 9, g32p_row19_traceSegment_094_0954_0009, g32p_row19_traceSegment_094_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 936 18 18, g32p_row19_traceSegment_094_0936_0018, g32p_row19_traceSegment_094_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 981 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 972 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 972 9 9, g32p_row19_traceSegment_094_0972_0009, g32p_row19_traceSegment_094_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 990 9 9, g32p_row19_traceSegment_094_0990_0009, g32p_row19_traceSegment_094_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 972 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 972 18 18, g32p_row19_traceSegment_094_0972_0018, g32p_row19_traceSegment_094_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 936 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 936 36 36, g32p_row19_traceSegment_094_0936_0036, g32p_row19_traceSegment_094_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 864 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 864 72 72, g32p_row19_traceSegment_094_0864_0072, g32p_row19_traceSegment_094_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1008 9 9, g32p_row19_traceSegment_094_1008_0009, g32p_row19_traceSegment_094_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1026 9 9, g32p_row19_traceSegment_094_1026_0009, g32p_row19_traceSegment_094_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1008 18 18, g32p_row19_traceSegment_094_1008_0018, g32p_row19_traceSegment_094_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1044 9 9, g32p_row19_traceSegment_094_1044_0009, g32p_row19_traceSegment_094_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1062 9 9, g32p_row19_traceSegment_094_1062_0009, g32p_row19_traceSegment_094_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1044 18 18, g32p_row19_traceSegment_094_1044_0018, g32p_row19_traceSegment_094_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1008 36 36, g32p_row19_traceSegment_094_1008_0036, g32p_row19_traceSegment_094_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1080 9 9, g32p_row19_traceSegment_094_1080_0009, g32p_row19_traceSegment_094_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1098 9 9, g32p_row19_traceSegment_094_1098_0009, g32p_row19_traceSegment_094_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1080 18 18, g32p_row19_traceSegment_094_1080_0018, g32p_row19_traceSegment_094_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1116 9 9, g32p_row19_traceSegment_094_1116_0009, g32p_row19_traceSegment_094_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_094 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_094_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_094 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1134 9 9, g32p_row19_traceSegment_094_1134_0009, g32p_row19_traceSegment_094_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_094 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1116 18 18, g32p_row19_traceSegment_094_1116_0018, g32p_row19_traceSegment_094_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_094 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1080 36 36, g32p_row19_traceSegment_094_1080_0036, g32p_row19_traceSegment_094_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_094_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_094 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 1008 72 72, g32p_row19_traceSegment_094_1008_0072, g32p_row19_traceSegment_094_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_094 864 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 864 144 144, g32p_row19_traceSegment_094_0864_0144, g32p_row19_traceSegment_094_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_094 576 576 = [5] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 576 288 288, g32p_row19_traceSegment_094_0576_0288, g32p_row19_traceSegment_094_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_094_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_094 0 1152 = [12] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_094 0 576 576, g32p_row19_traceSegment_094_0000_0576, g32p_row19_traceSegment_094_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 94 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_094_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row19_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 69) (g32p_literalTraceValue 18 69)
      [1, -1, 1] [2304, 2304] = true := by
  rw [g32p_row19_traceCoefficients_069]
  decide +kernel

theorem g32p_row19_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 74) (g32p_literalTraceValue 18 74)
      [1, -1, 1] [3456, 3456, 6912, 3456] = true := by
  rw [g32p_row19_traceCoefficients_074]
  decide +kernel

theorem g32p_row19_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 78) (g32p_literalTraceValue 18 78)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row19_traceCoefficients_078]
  decide +kernel

theorem g32p_row19_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 82) (g32p_literalTraceValue 18 82)
      [1, -1, 1] [0, 0, 13824, 13824] = true := by
  rw [g32p_row19_traceCoefficients_082]
  decide +kernel

theorem g32p_row19_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 83) (g32p_literalTraceValue 18 83)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_083]
  decide +kernel

theorem g32p_row19_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 90) (g32p_literalTraceValue 18 90)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row19_traceCoefficients_090]
  decide +kernel

theorem g32p_row19_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 92) (g32p_literalTraceValue 18 92)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_092]
  decide +kernel

theorem g32p_row19_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 94) (g32p_literalTraceValue 18 94)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_094]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
