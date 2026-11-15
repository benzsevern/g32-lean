import HodgeLean.Foundations.Program.G32PropFourSixPacked0401
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0402

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_065_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 9 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 0 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 0 9 9, g32p_row26_traceSegment_065_0000_0009, g32p_row26_traceSegment_065_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 18 9 9, g32p_row26_traceSegment_065_0018_0009, g32p_row26_traceSegment_065_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 0 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 0 18 18, g32p_row26_traceSegment_065_0000_0018, g32p_row26_traceSegment_065_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 36 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 36 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 36 9 9, g32p_row26_traceSegment_065_0036_0009, g32p_row26_traceSegment_065_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 54 9 9, g32p_row26_traceSegment_065_0054_0009, g32p_row26_traceSegment_065_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 36 18 18, g32p_row26_traceSegment_065_0036_0018, g32p_row26_traceSegment_065_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 0 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 0 36 36, g32p_row26_traceSegment_065_0000_0036, g32p_row26_traceSegment_065_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 72 9 9, g32p_row26_traceSegment_065_0072_0009, g32p_row26_traceSegment_065_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 90 9 9, g32p_row26_traceSegment_065_0090_0009, g32p_row26_traceSegment_065_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 72 18 18, g32p_row26_traceSegment_065_0072_0018, g32p_row26_traceSegment_065_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 108 9 9, g32p_row26_traceSegment_065_0108_0009, g32p_row26_traceSegment_065_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 126 9 9, g32p_row26_traceSegment_065_0126_0009, g32p_row26_traceSegment_065_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 108 18 18, g32p_row26_traceSegment_065_0108_0018, g32p_row26_traceSegment_065_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 72 36 36, g32p_row26_traceSegment_065_0072_0036, g32p_row26_traceSegment_065_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_065 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 0 72 72, g32p_row26_traceSegment_065_0000_0072, g32p_row26_traceSegment_065_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 144 9 9, g32p_row26_traceSegment_065_0144_0009, g32p_row26_traceSegment_065_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 162 9 9, g32p_row26_traceSegment_065_0162_0009, g32p_row26_traceSegment_065_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 144 18 18, g32p_row26_traceSegment_065_0144_0018, g32p_row26_traceSegment_065_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 180 9 9, g32p_row26_traceSegment_065_0180_0009, g32p_row26_traceSegment_065_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 198 9 9, g32p_row26_traceSegment_065_0198_0009, g32p_row26_traceSegment_065_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 180 18 18, g32p_row26_traceSegment_065_0180_0018, g32p_row26_traceSegment_065_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 144 36 36, g32p_row26_traceSegment_065_0144_0036, g32p_row26_traceSegment_065_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 216 9 9, g32p_row26_traceSegment_065_0216_0009, g32p_row26_traceSegment_065_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 234 9 9, g32p_row26_traceSegment_065_0234_0009, g32p_row26_traceSegment_065_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 216 18 18, g32p_row26_traceSegment_065_0216_0018, g32p_row26_traceSegment_065_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 252 9 9, g32p_row26_traceSegment_065_0252_0009, g32p_row26_traceSegment_065_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 270 9 9, g32p_row26_traceSegment_065_0270_0009, g32p_row26_traceSegment_065_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 252 18 18, g32p_row26_traceSegment_065_0252_0018, g32p_row26_traceSegment_065_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 216 36 36, g32p_row26_traceSegment_065_0216_0036, g32p_row26_traceSegment_065_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_065 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 144 72 72, g32p_row26_traceSegment_065_0144_0072, g32p_row26_traceSegment_065_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_065 0 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 0 144 144, g32p_row26_traceSegment_065_0000_0144, g32p_row26_traceSegment_065_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 288 9 9, g32p_row26_traceSegment_065_0288_0009, g32p_row26_traceSegment_065_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 306 9 9, g32p_row26_traceSegment_065_0306_0009, g32p_row26_traceSegment_065_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 288 18 18, g32p_row26_traceSegment_065_0288_0018, g32p_row26_traceSegment_065_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 324 9 9, g32p_row26_traceSegment_065_0324_0009, g32p_row26_traceSegment_065_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 342 9 9, g32p_row26_traceSegment_065_0342_0009, g32p_row26_traceSegment_065_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 324 18 18, g32p_row26_traceSegment_065_0324_0018, g32p_row26_traceSegment_065_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 288 36 36, g32p_row26_traceSegment_065_0288_0036, g32p_row26_traceSegment_065_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 360 9 9, g32p_row26_traceSegment_065_0360_0009, g32p_row26_traceSegment_065_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 378 9 9, g32p_row26_traceSegment_065_0378_0009, g32p_row26_traceSegment_065_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 360 18 18, g32p_row26_traceSegment_065_0360_0018, g32p_row26_traceSegment_065_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 396 9 9, g32p_row26_traceSegment_065_0396_0009, g32p_row26_traceSegment_065_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 414 9 9, g32p_row26_traceSegment_065_0414_0009, g32p_row26_traceSegment_065_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 396 18 18, g32p_row26_traceSegment_065_0396_0018, g32p_row26_traceSegment_065_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 360 36 36, g32p_row26_traceSegment_065_0360_0036, g32p_row26_traceSegment_065_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_065 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 288 72 72, g32p_row26_traceSegment_065_0288_0072, g32p_row26_traceSegment_065_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 432 9 9, g32p_row26_traceSegment_065_0432_0009, g32p_row26_traceSegment_065_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 450 9 9, g32p_row26_traceSegment_065_0450_0009, g32p_row26_traceSegment_065_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 432 18 18, g32p_row26_traceSegment_065_0432_0018, g32p_row26_traceSegment_065_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 468 9 9, g32p_row26_traceSegment_065_0468_0009, g32p_row26_traceSegment_065_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 486 9 9, g32p_row26_traceSegment_065_0486_0009, g32p_row26_traceSegment_065_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 468 18 18, g32p_row26_traceSegment_065_0468_0018, g32p_row26_traceSegment_065_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 432 36 36, g32p_row26_traceSegment_065_0432_0036, g32p_row26_traceSegment_065_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 504 9 9, g32p_row26_traceSegment_065_0504_0009, g32p_row26_traceSegment_065_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 522 9 9, g32p_row26_traceSegment_065_0522_0009, g32p_row26_traceSegment_065_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 504 18 18, g32p_row26_traceSegment_065_0504_0018, g32p_row26_traceSegment_065_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 540 9 9, g32p_row26_traceSegment_065_0540_0009, g32p_row26_traceSegment_065_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_065 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_065_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_065 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 558 9 9, g32p_row26_traceSegment_065_0558_0009, g32p_row26_traceSegment_065_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_065 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 540 18 18, g32p_row26_traceSegment_065_0540_0018, g32p_row26_traceSegment_065_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_065 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 504 36 36, g32p_row26_traceSegment_065_0504_0036, g32p_row26_traceSegment_065_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_065 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 432 72 72, g32p_row26_traceSegment_065_0432_0072, g32p_row26_traceSegment_065_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_065 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 288 144 144, g32p_row26_traceSegment_065_0288_0144, g32p_row26_traceSegment_065_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_065_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_065 0 576 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_065 0 288 288, g32p_row26_traceSegment_065_0000_0288, g32p_row26_traceSegment_065_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 65 = [0, 0, 0, 0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_065_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_067_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 0 9 9, g32p_row26_traceSegment_067_0000_0009, g32p_row26_traceSegment_067_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 18 9 9, g32p_row26_traceSegment_067_0018_0009, g32p_row26_traceSegment_067_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 0 18 18, g32p_row26_traceSegment_067_0000_0018, g32p_row26_traceSegment_067_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 36 9 9, g32p_row26_traceSegment_067_0036_0009, g32p_row26_traceSegment_067_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 54 9 9, g32p_row26_traceSegment_067_0054_0009, g32p_row26_traceSegment_067_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 36 18 18, g32p_row26_traceSegment_067_0036_0018, g32p_row26_traceSegment_067_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 0 36 36, g32p_row26_traceSegment_067_0000_0036, g32p_row26_traceSegment_067_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 72 9 9, g32p_row26_traceSegment_067_0072_0009, g32p_row26_traceSegment_067_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 90 9 9, g32p_row26_traceSegment_067_0090_0009, g32p_row26_traceSegment_067_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 72 18 18, g32p_row26_traceSegment_067_0072_0018, g32p_row26_traceSegment_067_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 108 9 9, g32p_row26_traceSegment_067_0108_0009, g32p_row26_traceSegment_067_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 126 9 9, g32p_row26_traceSegment_067_0126_0009, g32p_row26_traceSegment_067_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 108 18 18, g32p_row26_traceSegment_067_0108_0018, g32p_row26_traceSegment_067_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 72 36 36, g32p_row26_traceSegment_067_0072_0036, g32p_row26_traceSegment_067_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_067 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 0 72 72, g32p_row26_traceSegment_067_0000_0072, g32p_row26_traceSegment_067_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 144 9 9, g32p_row26_traceSegment_067_0144_0009, g32p_row26_traceSegment_067_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 171 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 162 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 162 9 9, g32p_row26_traceSegment_067_0162_0009, g32p_row26_traceSegment_067_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 144 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 144 18 18, g32p_row26_traceSegment_067_0144_0018, g32p_row26_traceSegment_067_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 180 9 9, g32p_row26_traceSegment_067_0180_0009, g32p_row26_traceSegment_067_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 207 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 198 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 198 9 9, g32p_row26_traceSegment_067_0198_0009, g32p_row26_traceSegment_067_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 180 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 180 18 18, g32p_row26_traceSegment_067_0180_0018, g32p_row26_traceSegment_067_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 144 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 144 36 36, g32p_row26_traceSegment_067_0144_0036, g32p_row26_traceSegment_067_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 216 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 216 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 216 9 9, g32p_row26_traceSegment_067_0216_0009, g32p_row26_traceSegment_067_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 234 9 9, g32p_row26_traceSegment_067_0234_0009, g32p_row26_traceSegment_067_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 216 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 216 18 18, g32p_row26_traceSegment_067_0216_0018, g32p_row26_traceSegment_067_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 252 9 9, g32p_row26_traceSegment_067_0252_0009, g32p_row26_traceSegment_067_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 270 9 9, g32p_row26_traceSegment_067_0270_0009, g32p_row26_traceSegment_067_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 252 18 18, g32p_row26_traceSegment_067_0252_0018, g32p_row26_traceSegment_067_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 216 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 216 36 36, g32p_row26_traceSegment_067_0216_0036, g32p_row26_traceSegment_067_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_067 144 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 144 72 72, g32p_row26_traceSegment_067_0144_0072, g32p_row26_traceSegment_067_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_067 0 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 0 144 144, g32p_row26_traceSegment_067_0000_0144, g32p_row26_traceSegment_067_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 288 9 9, g32p_row26_traceSegment_067_0288_0009, g32p_row26_traceSegment_067_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 306 9 9, g32p_row26_traceSegment_067_0306_0009, g32p_row26_traceSegment_067_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 288 18 18, g32p_row26_traceSegment_067_0288_0018, g32p_row26_traceSegment_067_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 324 9 9, g32p_row26_traceSegment_067_0324_0009, g32p_row26_traceSegment_067_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 342 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 342 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 342 9 9, g32p_row26_traceSegment_067_0342_0009, g32p_row26_traceSegment_067_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 324 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 324 18 18, g32p_row26_traceSegment_067_0324_0018, g32p_row26_traceSegment_067_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 288 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 288 36 36, g32p_row26_traceSegment_067_0288_0036, g32p_row26_traceSegment_067_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 360 9 9, g32p_row26_traceSegment_067_0360_0009, g32p_row26_traceSegment_067_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 378 9 9, g32p_row26_traceSegment_067_0378_0009, g32p_row26_traceSegment_067_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 360 18 18, g32p_row26_traceSegment_067_0360_0018, g32p_row26_traceSegment_067_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 396 9 9, g32p_row26_traceSegment_067_0396_0009, g32p_row26_traceSegment_067_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 414 9 9, g32p_row26_traceSegment_067_0414_0009, g32p_row26_traceSegment_067_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 396 18 18, g32p_row26_traceSegment_067_0396_0018, g32p_row26_traceSegment_067_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 360 36 36, g32p_row26_traceSegment_067_0360_0036, g32p_row26_traceSegment_067_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_067 288 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 288 72 72, g32p_row26_traceSegment_067_0288_0072, g32p_row26_traceSegment_067_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 432 9 9, g32p_row26_traceSegment_067_0432_0009, g32p_row26_traceSegment_067_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 450 9 9, g32p_row26_traceSegment_067_0450_0009, g32p_row26_traceSegment_067_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 432 18 18, g32p_row26_traceSegment_067_0432_0018, g32p_row26_traceSegment_067_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 468 9 9, g32p_row26_traceSegment_067_0468_0009, g32p_row26_traceSegment_067_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 486 9 9, g32p_row26_traceSegment_067_0486_0009, g32p_row26_traceSegment_067_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 468 18 18, g32p_row26_traceSegment_067_0468_0018, g32p_row26_traceSegment_067_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 432 36 36, g32p_row26_traceSegment_067_0432_0036, g32p_row26_traceSegment_067_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 504 9 9, g32p_row26_traceSegment_067_0504_0009, g32p_row26_traceSegment_067_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 522 9 9, g32p_row26_traceSegment_067_0522_0009, g32p_row26_traceSegment_067_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 504 18 18, g32p_row26_traceSegment_067_0504_0018, g32p_row26_traceSegment_067_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 540 9 9, g32p_row26_traceSegment_067_0540_0009, g32p_row26_traceSegment_067_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_067 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_067_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_067 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 558 9 9, g32p_row26_traceSegment_067_0558_0009, g32p_row26_traceSegment_067_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_067 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 540 18 18, g32p_row26_traceSegment_067_0540_0018, g32p_row26_traceSegment_067_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_067 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 504 36 36, g32p_row26_traceSegment_067_0504_0036, g32p_row26_traceSegment_067_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_067 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 432 72 72, g32p_row26_traceSegment_067_0432_0072, g32p_row26_traceSegment_067_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_067 288 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 288 144 144, g32p_row26_traceSegment_067_0288_0144, g32p_row26_traceSegment_067_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_067_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_067 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_067 0 288 288, g32p_row26_traceSegment_067_0000_0288, g32p_row26_traceSegment_067_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_067_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_069_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 0 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 0 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 0 9 9, g32p_row26_traceSegment_069_0000_0009, g32p_row26_traceSegment_069_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 27 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 18 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 18 9 9, g32p_row26_traceSegment_069_0018_0009, g32p_row26_traceSegment_069_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 0 36 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 0 18 18, g32p_row26_traceSegment_069_0000_0018, g32p_row26_traceSegment_069_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 36 9 9, g32p_row26_traceSegment_069_0036_0009, g32p_row26_traceSegment_069_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 63 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 54 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 54 9 9, g32p_row26_traceSegment_069_0054_0009, g32p_row26_traceSegment_069_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 36 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 36 18 18, g32p_row26_traceSegment_069_0036_0018, g32p_row26_traceSegment_069_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 0 72 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 0 36 36, g32p_row26_traceSegment_069_0000_0036, g32p_row26_traceSegment_069_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 81 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 72 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 72 9 9, g32p_row26_traceSegment_069_0072_0009, g32p_row26_traceSegment_069_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 90 9 9, g32p_row26_traceSegment_069_0090_0009, g32p_row26_traceSegment_069_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 72 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 72 18 18, g32p_row26_traceSegment_069_0072_0018, g32p_row26_traceSegment_069_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 108 9 9, g32p_row26_traceSegment_069_0108_0009, g32p_row26_traceSegment_069_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 126 9 9, g32p_row26_traceSegment_069_0126_0009, g32p_row26_traceSegment_069_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 108 18 18, g32p_row26_traceSegment_069_0108_0018, g32p_row26_traceSegment_069_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 72 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 72 36 36, g32p_row26_traceSegment_069_0072_0036, g32p_row26_traceSegment_069_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_069 0 144 = [4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 0 72 72, g32p_row26_traceSegment_069_0000_0072, g32p_row26_traceSegment_069_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 144 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 144 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 144 9 9, g32p_row26_traceSegment_069_0144_0009, g32p_row26_traceSegment_069_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 162 9 9, g32p_row26_traceSegment_069_0162_0009, g32p_row26_traceSegment_069_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 144 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 144 18 18, g32p_row26_traceSegment_069_0144_0018, g32p_row26_traceSegment_069_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 180 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 180 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 180 9 9, g32p_row26_traceSegment_069_0180_0009, g32p_row26_traceSegment_069_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 198 9 9, g32p_row26_traceSegment_069_0198_0009, g32p_row26_traceSegment_069_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 180 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 180 18 18, g32p_row26_traceSegment_069_0180_0018, g32p_row26_traceSegment_069_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 144 72 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 144 36 36, g32p_row26_traceSegment_069_0144_0036, g32p_row26_traceSegment_069_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 225 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 216 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 216 9 9, g32p_row26_traceSegment_069_0216_0009, g32p_row26_traceSegment_069_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 234 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 234 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 234 9 9, g32p_row26_traceSegment_069_0234_0009, g32p_row26_traceSegment_069_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 216 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 216 18 18, g32p_row26_traceSegment_069_0216_0018, g32p_row26_traceSegment_069_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 252 9 9, g32p_row26_traceSegment_069_0252_0009, g32p_row26_traceSegment_069_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 270 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 270 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 270 9 9, g32p_row26_traceSegment_069_0270_0009, g32p_row26_traceSegment_069_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 252 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 252 18 18, g32p_row26_traceSegment_069_0252_0018, g32p_row26_traceSegment_069_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 216 72 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 216 36 36, g32p_row26_traceSegment_069_0216_0036, g32p_row26_traceSegment_069_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_069 144 144 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 144 72 72, g32p_row26_traceSegment_069_0144_0072, g32p_row26_traceSegment_069_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_069 0 288 = [4, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 0 144 144, g32p_row26_traceSegment_069_0000_0144, g32p_row26_traceSegment_069_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 288 9 9, g32p_row26_traceSegment_069_0288_0009, g32p_row26_traceSegment_069_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 306 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 306 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 306 9 9, g32p_row26_traceSegment_069_0306_0009, g32p_row26_traceSegment_069_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 288 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 288 18 18, g32p_row26_traceSegment_069_0288_0018, g32p_row26_traceSegment_069_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 324 9 9, g32p_row26_traceSegment_069_0324_0009, g32p_row26_traceSegment_069_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 342 9 9, g32p_row26_traceSegment_069_0342_0009, g32p_row26_traceSegment_069_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 324 18 18, g32p_row26_traceSegment_069_0324_0018, g32p_row26_traceSegment_069_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 288 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 288 36 36, g32p_row26_traceSegment_069_0288_0036, g32p_row26_traceSegment_069_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 360 9 9, g32p_row26_traceSegment_069_0360_0009, g32p_row26_traceSegment_069_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 378 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 387 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 378 18 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 378 9 9, g32p_row26_traceSegment_069_0378_0009, g32p_row26_traceSegment_069_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 360 36 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 360 18 18, g32p_row26_traceSegment_069_0360_0018, g32p_row26_traceSegment_069_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 396 9 9, g32p_row26_traceSegment_069_0396_0009, g32p_row26_traceSegment_069_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 414 9 9, g32p_row26_traceSegment_069_0414_0009, g32p_row26_traceSegment_069_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 396 18 18, g32p_row26_traceSegment_069_0396_0018, g32p_row26_traceSegment_069_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 360 72 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 360 36 36, g32p_row26_traceSegment_069_0360_0036, g32p_row26_traceSegment_069_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_069 288 144 = [4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 288 72 72, g32p_row26_traceSegment_069_0288_0072, g32p_row26_traceSegment_069_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 432 9 9, g32p_row26_traceSegment_069_0432_0009, g32p_row26_traceSegment_069_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 450 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 450 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 450 9 9, g32p_row26_traceSegment_069_0450_0009, g32p_row26_traceSegment_069_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 432 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 432 18 18, g32p_row26_traceSegment_069_0432_0018, g32p_row26_traceSegment_069_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 468 9 9, g32p_row26_traceSegment_069_0468_0009, g32p_row26_traceSegment_069_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 486 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 486 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 486 9 9, g32p_row26_traceSegment_069_0486_0009, g32p_row26_traceSegment_069_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 468 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 468 18 18, g32p_row26_traceSegment_069_0468_0018, g32p_row26_traceSegment_069_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 432 72 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 432 36 36, g32p_row26_traceSegment_069_0432_0036, g32p_row26_traceSegment_069_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 504 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 513 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 504 18 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 504 9 9, g32p_row26_traceSegment_069_0504_0009, g32p_row26_traceSegment_069_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 522 9 = [2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 522 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 522 9 9, g32p_row26_traceSegment_069_0522_0009, g32p_row26_traceSegment_069_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 504 36 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 504 18 18, g32p_row26_traceSegment_069_0504_0018, g32p_row26_traceSegment_069_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 540 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 549 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 540 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 540 9 9, g32p_row26_traceSegment_069_0540_0009, g32p_row26_traceSegment_069_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 558 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_069 567 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_069_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_069 558 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 558 9 9, g32p_row26_traceSegment_069_0558_0009, g32p_row26_traceSegment_069_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_069 540 36 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 540 18 18, g32p_row26_traceSegment_069_0540_0018, g32p_row26_traceSegment_069_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_069 504 72 = [4, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 504 36 36, g32p_row26_traceSegment_069_0504_0036, g32p_row26_traceSegment_069_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_069 432 144 = [4, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 432 72 72, g32p_row26_traceSegment_069_0432_0072, g32p_row26_traceSegment_069_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_069 288 288 = [8, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 288 144 144, g32p_row26_traceSegment_069_0288_0144, g32p_row26_traceSegment_069_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_069_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_069 0 576 = [12, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_069 0 288 288, g32p_row26_traceSegment_069_0000_0288, g32p_row26_traceSegment_069_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 69 = [12, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_069_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_072 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 72 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_072_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 9 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 0 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 0 9 9, g32p_row26_traceSegment_072_0000_0009, g32p_row26_traceSegment_072_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 18 9 9, g32p_row26_traceSegment_072_0018_0009, g32p_row26_traceSegment_072_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 0 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 0 18 18, g32p_row26_traceSegment_072_0000_0018, g32p_row26_traceSegment_072_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 36 9 9, g32p_row26_traceSegment_072_0036_0009, g32p_row26_traceSegment_072_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 54 9 9, g32p_row26_traceSegment_072_0054_0009, g32p_row26_traceSegment_072_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 36 18 18, g32p_row26_traceSegment_072_0036_0018, g32p_row26_traceSegment_072_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 0 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 0 36 36, g32p_row26_traceSegment_072_0000_0036, g32p_row26_traceSegment_072_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 72 9 9, g32p_row26_traceSegment_072_0072_0009, g32p_row26_traceSegment_072_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 90 9 9, g32p_row26_traceSegment_072_0090_0009, g32p_row26_traceSegment_072_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 72 18 18, g32p_row26_traceSegment_072_0072_0018, g32p_row26_traceSegment_072_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 108 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 117 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 108 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 108 9 9, g32p_row26_traceSegment_072_0108_0009, g32p_row26_traceSegment_072_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 135 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 126 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 126 9 9, g32p_row26_traceSegment_072_0126_0009, g32p_row26_traceSegment_072_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 108 36 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 108 18 18, g32p_row26_traceSegment_072_0108_0018, g32p_row26_traceSegment_072_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 72 72 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 72 36 36, g32p_row26_traceSegment_072_0072_0036, g32p_row26_traceSegment_072_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_072 0 144 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 0 72 72, g32p_row26_traceSegment_072_0000_0072, g32p_row26_traceSegment_072_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 153 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 144 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 144 9 9, g32p_row26_traceSegment_072_0144_0009, g32p_row26_traceSegment_072_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 162 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 162 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 162 9 9, g32p_row26_traceSegment_072_0162_0009, g32p_row26_traceSegment_072_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 144 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 144 18 18, g32p_row26_traceSegment_072_0144_0018, g32p_row26_traceSegment_072_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 180 9 9, g32p_row26_traceSegment_072_0180_0009, g32p_row26_traceSegment_072_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 198 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 198 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 198 9 9, g32p_row26_traceSegment_072_0198_0009, g32p_row26_traceSegment_072_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 180 18 18, g32p_row26_traceSegment_072_0180_0018, g32p_row26_traceSegment_072_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 144 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 144 36 36, g32p_row26_traceSegment_072_0144_0036, g32p_row26_traceSegment_072_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 216 9 9, g32p_row26_traceSegment_072_0216_0009, g32p_row26_traceSegment_072_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 234 9 9, g32p_row26_traceSegment_072_0234_0009, g32p_row26_traceSegment_072_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 216 18 18, g32p_row26_traceSegment_072_0216_0018, g32p_row26_traceSegment_072_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 252 9 9, g32p_row26_traceSegment_072_0252_0009, g32p_row26_traceSegment_072_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 270 9 9, g32p_row26_traceSegment_072_0270_0009, g32p_row26_traceSegment_072_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 252 18 18, g32p_row26_traceSegment_072_0252_0018, g32p_row26_traceSegment_072_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 216 36 36, g32p_row26_traceSegment_072_0216_0036, g32p_row26_traceSegment_072_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_072 144 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 144 72 72, g32p_row26_traceSegment_072_0144_0072, g32p_row26_traceSegment_072_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_072 0 288 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 0 144 144, g32p_row26_traceSegment_072_0000_0144, g32p_row26_traceSegment_072_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 288 9 9, g32p_row26_traceSegment_072_0288_0009, g32p_row26_traceSegment_072_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 315 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 306 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 306 9 9, g32p_row26_traceSegment_072_0306_0009, g32p_row26_traceSegment_072_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 288 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 288 18 18, g32p_row26_traceSegment_072_0288_0018, g32p_row26_traceSegment_072_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 324 9 9, g32p_row26_traceSegment_072_0324_0009, g32p_row26_traceSegment_072_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 351 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 342 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 342 9 9, g32p_row26_traceSegment_072_0342_0009, g32p_row26_traceSegment_072_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 324 18 18, g32p_row26_traceSegment_072_0324_0018, g32p_row26_traceSegment_072_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 288 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 288 36 36, g32p_row26_traceSegment_072_0288_0036, g32p_row26_traceSegment_072_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 360 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 369 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 360 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 360 9 9, g32p_row26_traceSegment_072_0360_0009, g32p_row26_traceSegment_072_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 378 9 9, g32p_row26_traceSegment_072_0378_0009, g32p_row26_traceSegment_072_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 360 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 360 18 18, g32p_row26_traceSegment_072_0360_0018, g32p_row26_traceSegment_072_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 396 9 9, g32p_row26_traceSegment_072_0396_0009, g32p_row26_traceSegment_072_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 414 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 414 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 414 9 9, g32p_row26_traceSegment_072_0414_0009, g32p_row26_traceSegment_072_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 396 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 396 18 18, g32p_row26_traceSegment_072_0396_0018, g32p_row26_traceSegment_072_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 360 72 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 360 36 36, g32p_row26_traceSegment_072_0360_0036, g32p_row26_traceSegment_072_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_072 288 144 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 288 72 72, g32p_row26_traceSegment_072_0288_0072, g32p_row26_traceSegment_072_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 432 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 441 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 432 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 432 9 9, g32p_row26_traceSegment_072_0432_0009, g32p_row26_traceSegment_072_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 459 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 450 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 450 9 9, g32p_row26_traceSegment_072_0450_0009, g32p_row26_traceSegment_072_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 432 36 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 432 18 18, g32p_row26_traceSegment_072_0432_0018, g32p_row26_traceSegment_072_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 468 9 9, g32p_row26_traceSegment_072_0468_0009, g32p_row26_traceSegment_072_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 486 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 486 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 486 9 9, g32p_row26_traceSegment_072_0486_0009, g32p_row26_traceSegment_072_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 468 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 468 18 18, g32p_row26_traceSegment_072_0468_0018, g32p_row26_traceSegment_072_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 432 72 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 432 36 36, g32p_row26_traceSegment_072_0432_0036, g32p_row26_traceSegment_072_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 504 9 9, g32p_row26_traceSegment_072_0504_0009, g32p_row26_traceSegment_072_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 522 9 9, g32p_row26_traceSegment_072_0522_0009, g32p_row26_traceSegment_072_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 504 18 18, g32p_row26_traceSegment_072_0504_0018, g32p_row26_traceSegment_072_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 540 9 9, g32p_row26_traceSegment_072_0540_0009, g32p_row26_traceSegment_072_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_072 567 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_072_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_072 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 558 9 9, g32p_row26_traceSegment_072_0558_0009, g32p_row26_traceSegment_072_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_072 540 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 540 18 18, g32p_row26_traceSegment_072_0540_0018, g32p_row26_traceSegment_072_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_072 504 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 504 36 36, g32p_row26_traceSegment_072_0504_0036, g32p_row26_traceSegment_072_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_072 432 144 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 432 72 72, g32p_row26_traceSegment_072_0432_0072, g32p_row26_traceSegment_072_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_072 288 288 = [0, 10, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 288 144 144, g32p_row26_traceSegment_072_0288_0144, g32p_row26_traceSegment_072_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_072_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_072 0 576 = [0, 16, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_072 0 288 288, g32p_row26_traceSegment_072_0000_0288, g32p_row26_traceSegment_072_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 72 = [0, 16, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_072_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 58) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 58) (g32p_literalTraceValue 25 58)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_058]
  decide +kernel

theorem g32p_row26_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 61) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 61) (g32p_literalTraceValue 25 61)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_061]
  decide +kernel

theorem g32p_row26_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 63) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 63) (g32p_literalTraceValue 25 63)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_063]
  decide +kernel

theorem g32p_row26_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 64) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 64) (g32p_literalTraceValue 25 64)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_064]
  decide +kernel

theorem g32p_row26_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 65) (g32p_literalTraceValue 25 65)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row26_traceCoefficients_065]
  decide +kernel

theorem g32p_row26_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 67) (g32p_literalTraceValue 25 67)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row26_traceCoefficients_067]
  decide +kernel

theorem g32p_row26_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 69) (g32p_literalTraceValue 25 69)
      [1, -1, 1] [6912, 6912] = true := by
  rw [g32p_row26_traceCoefficients_069]
  decide +kernel

theorem g32p_row26_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 72) (g32p_literalTraceValue 25 72)
      [1, -1, 1] [-576, 576, 576] = true := by
  rw [g32p_row26_traceCoefficients_072]
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

private def g32p_row26_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_076_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 0 9 9, g32p_row26_traceSegment_076_0000_0009, g32p_row26_traceSegment_076_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 18 9 9, g32p_row26_traceSegment_076_0018_0009, g32p_row26_traceSegment_076_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 0 18 18, g32p_row26_traceSegment_076_0000_0018, g32p_row26_traceSegment_076_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 36 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 36 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 36 9 9, g32p_row26_traceSegment_076_0036_0009, g32p_row26_traceSegment_076_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 54 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 54 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 54 9 9, g32p_row26_traceSegment_076_0054_0009, g32p_row26_traceSegment_076_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 36 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 36 18 18, g32p_row26_traceSegment_076_0036_0018, g32p_row26_traceSegment_076_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 0 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 0 36 36, g32p_row26_traceSegment_076_0000_0036, g32p_row26_traceSegment_076_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 72 9 9, g32p_row26_traceSegment_076_0072_0009, g32p_row26_traceSegment_076_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 90 9 9, g32p_row26_traceSegment_076_0090_0009, g32p_row26_traceSegment_076_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 72 18 18, g32p_row26_traceSegment_076_0072_0018, g32p_row26_traceSegment_076_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 108 9 9, g32p_row26_traceSegment_076_0108_0009, g32p_row26_traceSegment_076_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 126 9 9, g32p_row26_traceSegment_076_0126_0009, g32p_row26_traceSegment_076_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 108 18 18, g32p_row26_traceSegment_076_0108_0018, g32p_row26_traceSegment_076_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 72 36 36, g32p_row26_traceSegment_076_0072_0036, g32p_row26_traceSegment_076_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_076 0 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 0 72 72, g32p_row26_traceSegment_076_0000_0072, g32p_row26_traceSegment_076_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 144 9 9, g32p_row26_traceSegment_076_0144_0009, g32p_row26_traceSegment_076_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 162 9 9, g32p_row26_traceSegment_076_0162_0009, g32p_row26_traceSegment_076_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 144 18 18, g32p_row26_traceSegment_076_0144_0018, g32p_row26_traceSegment_076_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 180 9 9, g32p_row26_traceSegment_076_0180_0009, g32p_row26_traceSegment_076_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 198 9 9, g32p_row26_traceSegment_076_0198_0009, g32p_row26_traceSegment_076_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 180 18 18, g32p_row26_traceSegment_076_0180_0018, g32p_row26_traceSegment_076_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 144 36 36, g32p_row26_traceSegment_076_0144_0036, g32p_row26_traceSegment_076_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 216 9 9, g32p_row26_traceSegment_076_0216_0009, g32p_row26_traceSegment_076_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 234 9 9, g32p_row26_traceSegment_076_0234_0009, g32p_row26_traceSegment_076_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 216 18 18, g32p_row26_traceSegment_076_0216_0018, g32p_row26_traceSegment_076_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 261 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 252 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 252 9 9, g32p_row26_traceSegment_076_0252_0009, g32p_row26_traceSegment_076_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 270 9 9, g32p_row26_traceSegment_076_0270_0009, g32p_row26_traceSegment_076_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 252 18 18, g32p_row26_traceSegment_076_0252_0018, g32p_row26_traceSegment_076_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 216 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 216 36 36, g32p_row26_traceSegment_076_0216_0036, g32p_row26_traceSegment_076_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_076 144 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 144 72 72, g32p_row26_traceSegment_076_0144_0072, g32p_row26_traceSegment_076_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_076 0 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 0 144 144, g32p_row26_traceSegment_076_0000_0144, g32p_row26_traceSegment_076_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 288 9 9, g32p_row26_traceSegment_076_0288_0009, g32p_row26_traceSegment_076_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 306 9 9, g32p_row26_traceSegment_076_0306_0009, g32p_row26_traceSegment_076_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 288 18 18, g32p_row26_traceSegment_076_0288_0018, g32p_row26_traceSegment_076_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 324 9 9, g32p_row26_traceSegment_076_0324_0009, g32p_row26_traceSegment_076_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 342 9 9, g32p_row26_traceSegment_076_0342_0009, g32p_row26_traceSegment_076_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 324 18 18, g32p_row26_traceSegment_076_0324_0018, g32p_row26_traceSegment_076_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 288 36 36, g32p_row26_traceSegment_076_0288_0036, g32p_row26_traceSegment_076_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 360 9 9, g32p_row26_traceSegment_076_0360_0009, g32p_row26_traceSegment_076_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 378 9 9, g32p_row26_traceSegment_076_0378_0009, g32p_row26_traceSegment_076_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 360 18 18, g32p_row26_traceSegment_076_0360_0018, g32p_row26_traceSegment_076_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 396 9 9, g32p_row26_traceSegment_076_0396_0009, g32p_row26_traceSegment_076_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 414 9 9, g32p_row26_traceSegment_076_0414_0009, g32p_row26_traceSegment_076_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 396 18 18, g32p_row26_traceSegment_076_0396_0018, g32p_row26_traceSegment_076_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 360 36 36, g32p_row26_traceSegment_076_0360_0036, g32p_row26_traceSegment_076_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_076 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 288 72 72, g32p_row26_traceSegment_076_0288_0072, g32p_row26_traceSegment_076_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 432 9 9, g32p_row26_traceSegment_076_0432_0009, g32p_row26_traceSegment_076_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 450 9 9, g32p_row26_traceSegment_076_0450_0009, g32p_row26_traceSegment_076_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 432 18 18, g32p_row26_traceSegment_076_0432_0018, g32p_row26_traceSegment_076_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 468 9 9, g32p_row26_traceSegment_076_0468_0009, g32p_row26_traceSegment_076_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 486 9 9, g32p_row26_traceSegment_076_0486_0009, g32p_row26_traceSegment_076_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 468 18 18, g32p_row26_traceSegment_076_0468_0018, g32p_row26_traceSegment_076_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 432 36 36, g32p_row26_traceSegment_076_0432_0036, g32p_row26_traceSegment_076_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 504 9 9, g32p_row26_traceSegment_076_0504_0009, g32p_row26_traceSegment_076_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 522 9 9, g32p_row26_traceSegment_076_0522_0009, g32p_row26_traceSegment_076_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 504 18 18, g32p_row26_traceSegment_076_0504_0018, g32p_row26_traceSegment_076_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 540 9 9, g32p_row26_traceSegment_076_0540_0009, g32p_row26_traceSegment_076_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_076 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_076_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_076 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 558 9 9, g32p_row26_traceSegment_076_0558_0009, g32p_row26_traceSegment_076_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_076 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 540 18 18, g32p_row26_traceSegment_076_0540_0018, g32p_row26_traceSegment_076_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_076 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 504 36 36, g32p_row26_traceSegment_076_0504_0036, g32p_row26_traceSegment_076_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_076 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 432 72 72, g32p_row26_traceSegment_076_0432_0072, g32p_row26_traceSegment_076_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_076 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 288 144 144, g32p_row26_traceSegment_076_0288_0144, g32p_row26_traceSegment_076_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_076_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_076 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_076 0 288 288, g32p_row26_traceSegment_076_0000_0288, g32p_row26_traceSegment_076_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 76 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_076_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_077 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 77 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_077_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 0 9 9, g32p_row26_traceSegment_077_0000_0009, g32p_row26_traceSegment_077_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 18 9 9, g32p_row26_traceSegment_077_0018_0009, g32p_row26_traceSegment_077_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 0 18 18, g32p_row26_traceSegment_077_0000_0018, g32p_row26_traceSegment_077_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 36 9 9, g32p_row26_traceSegment_077_0036_0009, g32p_row26_traceSegment_077_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 54 9 9, g32p_row26_traceSegment_077_0054_0009, g32p_row26_traceSegment_077_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 36 18 18, g32p_row26_traceSegment_077_0036_0018, g32p_row26_traceSegment_077_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 0 36 36, g32p_row26_traceSegment_077_0000_0036, g32p_row26_traceSegment_077_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 72 9 9, g32p_row26_traceSegment_077_0072_0009, g32p_row26_traceSegment_077_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 90 9 9, g32p_row26_traceSegment_077_0090_0009, g32p_row26_traceSegment_077_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 72 18 18, g32p_row26_traceSegment_077_0072_0018, g32p_row26_traceSegment_077_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 108 9 9, g32p_row26_traceSegment_077_0108_0009, g32p_row26_traceSegment_077_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 126 9 9, g32p_row26_traceSegment_077_0126_0009, g32p_row26_traceSegment_077_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 108 18 18, g32p_row26_traceSegment_077_0108_0018, g32p_row26_traceSegment_077_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 72 36 36, g32p_row26_traceSegment_077_0072_0036, g32p_row26_traceSegment_077_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_077 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 0 72 72, g32p_row26_traceSegment_077_0000_0072, g32p_row26_traceSegment_077_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 144 9 9, g32p_row26_traceSegment_077_0144_0009, g32p_row26_traceSegment_077_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 162 9 9, g32p_row26_traceSegment_077_0162_0009, g32p_row26_traceSegment_077_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 144 18 18, g32p_row26_traceSegment_077_0144_0018, g32p_row26_traceSegment_077_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 180 9 9, g32p_row26_traceSegment_077_0180_0009, g32p_row26_traceSegment_077_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 198 9 9, g32p_row26_traceSegment_077_0198_0009, g32p_row26_traceSegment_077_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 180 18 18, g32p_row26_traceSegment_077_0180_0018, g32p_row26_traceSegment_077_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 144 36 36, g32p_row26_traceSegment_077_0144_0036, g32p_row26_traceSegment_077_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 216 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 216 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 216 9 9, g32p_row26_traceSegment_077_0216_0009, g32p_row26_traceSegment_077_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 234 9 9, g32p_row26_traceSegment_077_0234_0009, g32p_row26_traceSegment_077_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 216 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 216 18 18, g32p_row26_traceSegment_077_0216_0018, g32p_row26_traceSegment_077_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 252 9 9, g32p_row26_traceSegment_077_0252_0009, g32p_row26_traceSegment_077_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 279 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 270 9 9, g32p_row26_traceSegment_077_0270_0009, g32p_row26_traceSegment_077_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 252 18 18, g32p_row26_traceSegment_077_0252_0018, g32p_row26_traceSegment_077_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 216 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 216 36 36, g32p_row26_traceSegment_077_0216_0036, g32p_row26_traceSegment_077_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_077 144 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 144 72 72, g32p_row26_traceSegment_077_0144_0072, g32p_row26_traceSegment_077_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_077 0 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 0 144 144, g32p_row26_traceSegment_077_0000_0144, g32p_row26_traceSegment_077_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 297 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 288 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 288 9 9, g32p_row26_traceSegment_077_0288_0009, g32p_row26_traceSegment_077_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 306 9 9, g32p_row26_traceSegment_077_0306_0009, g32p_row26_traceSegment_077_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 288 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 288 18 18, g32p_row26_traceSegment_077_0288_0018, g32p_row26_traceSegment_077_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 324 9 9, g32p_row26_traceSegment_077_0324_0009, g32p_row26_traceSegment_077_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 342 9 9, g32p_row26_traceSegment_077_0342_0009, g32p_row26_traceSegment_077_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 324 18 18, g32p_row26_traceSegment_077_0324_0018, g32p_row26_traceSegment_077_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 288 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 288 36 36, g32p_row26_traceSegment_077_0288_0036, g32p_row26_traceSegment_077_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 360 9 9, g32p_row26_traceSegment_077_0360_0009, g32p_row26_traceSegment_077_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 378 9 9, g32p_row26_traceSegment_077_0378_0009, g32p_row26_traceSegment_077_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 360 18 18, g32p_row26_traceSegment_077_0360_0018, g32p_row26_traceSegment_077_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 396 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 396 9 9, g32p_row26_traceSegment_077_0396_0009, g32p_row26_traceSegment_077_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 414 9 9, g32p_row26_traceSegment_077_0414_0009, g32p_row26_traceSegment_077_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 396 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 396 18 18, g32p_row26_traceSegment_077_0396_0018, g32p_row26_traceSegment_077_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 360 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 360 36 36, g32p_row26_traceSegment_077_0360_0036, g32p_row26_traceSegment_077_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_077 288 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 288 72 72, g32p_row26_traceSegment_077_0288_0072, g32p_row26_traceSegment_077_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 432 9 9, g32p_row26_traceSegment_077_0432_0009, g32p_row26_traceSegment_077_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 450 9 9, g32p_row26_traceSegment_077_0450_0009, g32p_row26_traceSegment_077_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 432 18 18, g32p_row26_traceSegment_077_0432_0018, g32p_row26_traceSegment_077_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 468 9 9, g32p_row26_traceSegment_077_0468_0009, g32p_row26_traceSegment_077_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 486 9 9, g32p_row26_traceSegment_077_0486_0009, g32p_row26_traceSegment_077_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 468 18 18, g32p_row26_traceSegment_077_0468_0018, g32p_row26_traceSegment_077_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 432 36 36, g32p_row26_traceSegment_077_0432_0036, g32p_row26_traceSegment_077_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 504 9 9, g32p_row26_traceSegment_077_0504_0009, g32p_row26_traceSegment_077_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 522 9 9, g32p_row26_traceSegment_077_0522_0009, g32p_row26_traceSegment_077_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 504 18 18, g32p_row26_traceSegment_077_0504_0018, g32p_row26_traceSegment_077_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 540 9 9, g32p_row26_traceSegment_077_0540_0009, g32p_row26_traceSegment_077_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_077 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_077_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_077 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 558 9 9, g32p_row26_traceSegment_077_0558_0009, g32p_row26_traceSegment_077_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_077 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 540 18 18, g32p_row26_traceSegment_077_0540_0018, g32p_row26_traceSegment_077_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_077 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 504 36 36, g32p_row26_traceSegment_077_0504_0036, g32p_row26_traceSegment_077_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_077 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 432 72 72, g32p_row26_traceSegment_077_0432_0072, g32p_row26_traceSegment_077_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_077 288 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 288 144 144, g32p_row26_traceSegment_077_0288_0144, g32p_row26_traceSegment_077_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_077_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_077 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_077 0 288 288, g32p_row26_traceSegment_077_0000_0288, g32p_row26_traceSegment_077_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 77 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_077_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_079 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 79 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_079_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 0 9 9, g32p_row26_traceSegment_079_0000_0009, g32p_row26_traceSegment_079_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 27 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 18 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 18 9 9, g32p_row26_traceSegment_079_0018_0009, g32p_row26_traceSegment_079_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 0 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 0 18 18, g32p_row26_traceSegment_079_0000_0018, g32p_row26_traceSegment_079_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 36 9 9, g32p_row26_traceSegment_079_0036_0009, g32p_row26_traceSegment_079_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 54 9 9, g32p_row26_traceSegment_079_0054_0009, g32p_row26_traceSegment_079_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 36 18 18, g32p_row26_traceSegment_079_0036_0018, g32p_row26_traceSegment_079_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 0 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 0 36 36, g32p_row26_traceSegment_079_0000_0036, g32p_row26_traceSegment_079_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 72 9 9, g32p_row26_traceSegment_079_0072_0009, g32p_row26_traceSegment_079_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 90 9 9, g32p_row26_traceSegment_079_0090_0009, g32p_row26_traceSegment_079_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 72 18 18, g32p_row26_traceSegment_079_0072_0018, g32p_row26_traceSegment_079_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 108 9 9, g32p_row26_traceSegment_079_0108_0009, g32p_row26_traceSegment_079_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 126 9 9, g32p_row26_traceSegment_079_0126_0009, g32p_row26_traceSegment_079_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 108 18 18, g32p_row26_traceSegment_079_0108_0018, g32p_row26_traceSegment_079_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 72 36 36, g32p_row26_traceSegment_079_0072_0036, g32p_row26_traceSegment_079_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_079 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 0 72 72, g32p_row26_traceSegment_079_0000_0072, g32p_row26_traceSegment_079_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 144 9 9, g32p_row26_traceSegment_079_0144_0009, g32p_row26_traceSegment_079_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 162 9 9, g32p_row26_traceSegment_079_0162_0009, g32p_row26_traceSegment_079_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 144 18 18, g32p_row26_traceSegment_079_0144_0018, g32p_row26_traceSegment_079_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 180 9 9, g32p_row26_traceSegment_079_0180_0009, g32p_row26_traceSegment_079_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 198 9 9, g32p_row26_traceSegment_079_0198_0009, g32p_row26_traceSegment_079_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 180 18 18, g32p_row26_traceSegment_079_0180_0018, g32p_row26_traceSegment_079_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 144 36 36, g32p_row26_traceSegment_079_0144_0036, g32p_row26_traceSegment_079_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 216 9 9, g32p_row26_traceSegment_079_0216_0009, g32p_row26_traceSegment_079_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 234 9 9, g32p_row26_traceSegment_079_0234_0009, g32p_row26_traceSegment_079_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 216 18 18, g32p_row26_traceSegment_079_0216_0018, g32p_row26_traceSegment_079_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 252 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 261 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 252 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 252 9 9, g32p_row26_traceSegment_079_0252_0009, g32p_row26_traceSegment_079_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 270 9 9, g32p_row26_traceSegment_079_0270_0009, g32p_row26_traceSegment_079_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 252 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 252 18 18, g32p_row26_traceSegment_079_0252_0018, g32p_row26_traceSegment_079_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 216 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 216 36 36, g32p_row26_traceSegment_079_0216_0036, g32p_row26_traceSegment_079_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_079 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 144 72 72, g32p_row26_traceSegment_079_0144_0072, g32p_row26_traceSegment_079_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_079 0 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 0 144 144, g32p_row26_traceSegment_079_0000_0144, g32p_row26_traceSegment_079_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 288 9 9, g32p_row26_traceSegment_079_0288_0009, g32p_row26_traceSegment_079_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 306 9 9, g32p_row26_traceSegment_079_0306_0009, g32p_row26_traceSegment_079_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 288 18 18, g32p_row26_traceSegment_079_0288_0018, g32p_row26_traceSegment_079_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 324 9 9, g32p_row26_traceSegment_079_0324_0009, g32p_row26_traceSegment_079_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 342 9 9, g32p_row26_traceSegment_079_0342_0009, g32p_row26_traceSegment_079_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 324 18 18, g32p_row26_traceSegment_079_0324_0018, g32p_row26_traceSegment_079_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 288 36 36, g32p_row26_traceSegment_079_0288_0036, g32p_row26_traceSegment_079_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 360 9 9, g32p_row26_traceSegment_079_0360_0009, g32p_row26_traceSegment_079_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 378 9 9, g32p_row26_traceSegment_079_0378_0009, g32p_row26_traceSegment_079_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 360 18 18, g32p_row26_traceSegment_079_0360_0018, g32p_row26_traceSegment_079_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 396 9 9, g32p_row26_traceSegment_079_0396_0009, g32p_row26_traceSegment_079_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 414 9 9, g32p_row26_traceSegment_079_0414_0009, g32p_row26_traceSegment_079_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 396 18 18, g32p_row26_traceSegment_079_0396_0018, g32p_row26_traceSegment_079_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 360 36 36, g32p_row26_traceSegment_079_0360_0036, g32p_row26_traceSegment_079_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_079 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 288 72 72, g32p_row26_traceSegment_079_0288_0072, g32p_row26_traceSegment_079_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 432 9 9, g32p_row26_traceSegment_079_0432_0009, g32p_row26_traceSegment_079_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 450 9 9, g32p_row26_traceSegment_079_0450_0009, g32p_row26_traceSegment_079_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 432 18 18, g32p_row26_traceSegment_079_0432_0018, g32p_row26_traceSegment_079_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 468 9 9, g32p_row26_traceSegment_079_0468_0009, g32p_row26_traceSegment_079_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 486 9 9, g32p_row26_traceSegment_079_0486_0009, g32p_row26_traceSegment_079_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 468 18 18, g32p_row26_traceSegment_079_0468_0018, g32p_row26_traceSegment_079_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 432 36 36, g32p_row26_traceSegment_079_0432_0036, g32p_row26_traceSegment_079_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 504 9 9, g32p_row26_traceSegment_079_0504_0009, g32p_row26_traceSegment_079_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 522 9 9, g32p_row26_traceSegment_079_0522_0009, g32p_row26_traceSegment_079_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 504 18 18, g32p_row26_traceSegment_079_0504_0018, g32p_row26_traceSegment_079_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 540 9 9, g32p_row26_traceSegment_079_0540_0009, g32p_row26_traceSegment_079_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_079 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_079_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_079 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 558 9 9, g32p_row26_traceSegment_079_0558_0009, g32p_row26_traceSegment_079_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_079 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 540 18 18, g32p_row26_traceSegment_079_0540_0018, g32p_row26_traceSegment_079_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_079 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 504 36 36, g32p_row26_traceSegment_079_0504_0036, g32p_row26_traceSegment_079_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_079 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 432 72 72, g32p_row26_traceSegment_079_0432_0072, g32p_row26_traceSegment_079_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_079 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 288 144 144, g32p_row26_traceSegment_079_0288_0144, g32p_row26_traceSegment_079_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_079_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_079 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_079 0 288 288, g32p_row26_traceSegment_079_0000_0288, g32p_row26_traceSegment_079_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 79 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_079_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_080 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 80 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_080_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 0 9 9, g32p_row26_traceSegment_080_0000_0009, g32p_row26_traceSegment_080_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 18 9 9, g32p_row26_traceSegment_080_0018_0009, g32p_row26_traceSegment_080_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 0 18 18, g32p_row26_traceSegment_080_0000_0018, g32p_row26_traceSegment_080_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 36 9 9, g32p_row26_traceSegment_080_0036_0009, g32p_row26_traceSegment_080_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 54 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 54 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 54 9 9, g32p_row26_traceSegment_080_0054_0009, g32p_row26_traceSegment_080_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 36 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 36 18 18, g32p_row26_traceSegment_080_0036_0018, g32p_row26_traceSegment_080_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 0 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 0 36 36, g32p_row26_traceSegment_080_0000_0036, g32p_row26_traceSegment_080_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 81 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 72 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 72 9 9, g32p_row26_traceSegment_080_0072_0009, g32p_row26_traceSegment_080_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 90 9 9, g32p_row26_traceSegment_080_0090_0009, g32p_row26_traceSegment_080_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 72 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 72 18 18, g32p_row26_traceSegment_080_0072_0018, g32p_row26_traceSegment_080_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 108 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 117 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 108 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 108 9 9, g32p_row26_traceSegment_080_0108_0009, g32p_row26_traceSegment_080_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 126 9 9, g32p_row26_traceSegment_080_0126_0009, g32p_row26_traceSegment_080_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 108 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 108 18 18, g32p_row26_traceSegment_080_0108_0018, g32p_row26_traceSegment_080_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 72 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 72 36 36, g32p_row26_traceSegment_080_0072_0036, g32p_row26_traceSegment_080_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_080 0 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 0 72 72, g32p_row26_traceSegment_080_0000_0072, g32p_row26_traceSegment_080_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 144 9 9, g32p_row26_traceSegment_080_0144_0009, g32p_row26_traceSegment_080_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 162 9 9, g32p_row26_traceSegment_080_0162_0009, g32p_row26_traceSegment_080_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 144 18 18, g32p_row26_traceSegment_080_0144_0018, g32p_row26_traceSegment_080_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 180 9 9, g32p_row26_traceSegment_080_0180_0009, g32p_row26_traceSegment_080_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 207 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 198 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 198 9 9, g32p_row26_traceSegment_080_0198_0009, g32p_row26_traceSegment_080_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 180 18 18, g32p_row26_traceSegment_080_0180_0018, g32p_row26_traceSegment_080_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 144 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 144 36 36, g32p_row26_traceSegment_080_0144_0036, g32p_row26_traceSegment_080_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 216 9 9, g32p_row26_traceSegment_080_0216_0009, g32p_row26_traceSegment_080_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 234 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 234 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 234 9 9, g32p_row26_traceSegment_080_0234_0009, g32p_row26_traceSegment_080_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 216 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 216 18 18, g32p_row26_traceSegment_080_0216_0018, g32p_row26_traceSegment_080_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 252 9 9, g32p_row26_traceSegment_080_0252_0009, g32p_row26_traceSegment_080_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 270 9 9, g32p_row26_traceSegment_080_0270_0009, g32p_row26_traceSegment_080_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 252 18 18, g32p_row26_traceSegment_080_0252_0018, g32p_row26_traceSegment_080_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 216 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 216 36 36, g32p_row26_traceSegment_080_0216_0036, g32p_row26_traceSegment_080_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_080 144 144 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 144 72 72, g32p_row26_traceSegment_080_0144_0072, g32p_row26_traceSegment_080_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_080 0 288 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 0 144 144, g32p_row26_traceSegment_080_0000_0144, g32p_row26_traceSegment_080_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 288 9 9, g32p_row26_traceSegment_080_0288_0009, g32p_row26_traceSegment_080_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 306 9 9, g32p_row26_traceSegment_080_0306_0009, g32p_row26_traceSegment_080_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 288 18 18, g32p_row26_traceSegment_080_0288_0018, g32p_row26_traceSegment_080_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 324 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 333 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 324 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 324 9 9, g32p_row26_traceSegment_080_0324_0009, g32p_row26_traceSegment_080_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 342 9 9, g32p_row26_traceSegment_080_0342_0009, g32p_row26_traceSegment_080_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 324 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 324 18 18, g32p_row26_traceSegment_080_0324_0018, g32p_row26_traceSegment_080_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 288 72 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 288 36 36, g32p_row26_traceSegment_080_0288_0036, g32p_row26_traceSegment_080_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 369 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 360 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 360 9 9, g32p_row26_traceSegment_080_0360_0009, g32p_row26_traceSegment_080_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 378 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 387 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 378 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 378 9 9, g32p_row26_traceSegment_080_0378_0009, g32p_row26_traceSegment_080_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 360 36 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 360 18 18, g32p_row26_traceSegment_080_0360_0018, g32p_row26_traceSegment_080_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 405 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 396 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 396 9 9, g32p_row26_traceSegment_080_0396_0009, g32p_row26_traceSegment_080_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 423 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 414 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 414 9 9, g32p_row26_traceSegment_080_0414_0009, g32p_row26_traceSegment_080_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 396 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 396 18 18, g32p_row26_traceSegment_080_0396_0018, g32p_row26_traceSegment_080_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 360 72 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 360 36 36, g32p_row26_traceSegment_080_0360_0036, g32p_row26_traceSegment_080_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_080 288 144 = [0, 5, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 288 72 72, g32p_row26_traceSegment_080_0288_0072, g32p_row26_traceSegment_080_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 432 9 9, g32p_row26_traceSegment_080_0432_0009, g32p_row26_traceSegment_080_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 450 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 450 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 450 9 9, g32p_row26_traceSegment_080_0450_0009, g32p_row26_traceSegment_080_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 432 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 432 18 18, g32p_row26_traceSegment_080_0432_0018, g32p_row26_traceSegment_080_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 468 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 468 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 468 9 9, g32p_row26_traceSegment_080_0468_0009, g32p_row26_traceSegment_080_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 495 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 486 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 486 9 9, g32p_row26_traceSegment_080_0486_0009, g32p_row26_traceSegment_080_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 468 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 468 18 18, g32p_row26_traceSegment_080_0468_0018, g32p_row26_traceSegment_080_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 432 72 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 432 36 36, g32p_row26_traceSegment_080_0432_0036, g32p_row26_traceSegment_080_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 504 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 504 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 504 9 9, g32p_row26_traceSegment_080_0504_0009, g32p_row26_traceSegment_080_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 522 9 9, g32p_row26_traceSegment_080_0522_0009, g32p_row26_traceSegment_080_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 504 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 504 18 18, g32p_row26_traceSegment_080_0504_0018, g32p_row26_traceSegment_080_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 540 9 9, g32p_row26_traceSegment_080_0540_0009, g32p_row26_traceSegment_080_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_080 567 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_080_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_080 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 558 9 9, g32p_row26_traceSegment_080_0558_0009, g32p_row26_traceSegment_080_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_080 540 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 540 18 18, g32p_row26_traceSegment_080_0540_0018, g32p_row26_traceSegment_080_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_080 504 72 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 504 36 36, g32p_row26_traceSegment_080_0504_0036, g32p_row26_traceSegment_080_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_080 432 144 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 432 72 72, g32p_row26_traceSegment_080_0432_0072, g32p_row26_traceSegment_080_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_080 288 288 = [0, 10, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 288 144 144, g32p_row26_traceSegment_080_0288_0144, g32p_row26_traceSegment_080_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_080_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_080 0 576 = [0, 16, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_080 0 288 288, g32p_row26_traceSegment_080_0000_0288, g32p_row26_traceSegment_080_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 80 = [0, 16, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_080_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_081 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 81 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_081_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 0 9 9, g32p_row26_traceSegment_081_0000_0009, g32p_row26_traceSegment_081_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 18 9 9, g32p_row26_traceSegment_081_0018_0009, g32p_row26_traceSegment_081_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 0 18 18, g32p_row26_traceSegment_081_0000_0018, g32p_row26_traceSegment_081_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 36 9 9, g32p_row26_traceSegment_081_0036_0009, g32p_row26_traceSegment_081_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 54 9 9, g32p_row26_traceSegment_081_0054_0009, g32p_row26_traceSegment_081_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 36 18 18, g32p_row26_traceSegment_081_0036_0018, g32p_row26_traceSegment_081_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 0 36 36, g32p_row26_traceSegment_081_0000_0036, g32p_row26_traceSegment_081_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 72 9 9, g32p_row26_traceSegment_081_0072_0009, g32p_row26_traceSegment_081_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 90 9 9, g32p_row26_traceSegment_081_0090_0009, g32p_row26_traceSegment_081_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 72 18 18, g32p_row26_traceSegment_081_0072_0018, g32p_row26_traceSegment_081_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 108 9 9, g32p_row26_traceSegment_081_0108_0009, g32p_row26_traceSegment_081_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 126 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 126 9 9, g32p_row26_traceSegment_081_0126_0009, g32p_row26_traceSegment_081_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 108 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 108 18 18, g32p_row26_traceSegment_081_0108_0018, g32p_row26_traceSegment_081_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 72 36 36, g32p_row26_traceSegment_081_0072_0036, g32p_row26_traceSegment_081_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_081 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 0 72 72, g32p_row26_traceSegment_081_0000_0072, g32p_row26_traceSegment_081_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 144 9 9, g32p_row26_traceSegment_081_0144_0009, g32p_row26_traceSegment_081_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 162 9 9, g32p_row26_traceSegment_081_0162_0009, g32p_row26_traceSegment_081_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 144 18 18, g32p_row26_traceSegment_081_0144_0018, g32p_row26_traceSegment_081_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 180 9 9, g32p_row26_traceSegment_081_0180_0009, g32p_row26_traceSegment_081_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 198 9 9, g32p_row26_traceSegment_081_0198_0009, g32p_row26_traceSegment_081_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 180 18 18, g32p_row26_traceSegment_081_0180_0018, g32p_row26_traceSegment_081_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 144 36 36, g32p_row26_traceSegment_081_0144_0036, g32p_row26_traceSegment_081_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 216 9 9, g32p_row26_traceSegment_081_0216_0009, g32p_row26_traceSegment_081_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 234 9 9, g32p_row26_traceSegment_081_0234_0009, g32p_row26_traceSegment_081_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 216 18 18, g32p_row26_traceSegment_081_0216_0018, g32p_row26_traceSegment_081_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 252 9 9, g32p_row26_traceSegment_081_0252_0009, g32p_row26_traceSegment_081_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 279 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 270 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 270 9 9, g32p_row26_traceSegment_081_0270_0009, g32p_row26_traceSegment_081_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 252 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 252 18 18, g32p_row26_traceSegment_081_0252_0018, g32p_row26_traceSegment_081_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 216 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 216 36 36, g32p_row26_traceSegment_081_0216_0036, g32p_row26_traceSegment_081_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_081 144 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 144 72 72, g32p_row26_traceSegment_081_0144_0072, g32p_row26_traceSegment_081_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_081 0 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 0 144 144, g32p_row26_traceSegment_081_0000_0144, g32p_row26_traceSegment_081_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 297 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 288 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 288 9 9, g32p_row26_traceSegment_081_0288_0009, g32p_row26_traceSegment_081_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 306 9 9, g32p_row26_traceSegment_081_0306_0009, g32p_row26_traceSegment_081_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 288 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 288 18 18, g32p_row26_traceSegment_081_0288_0018, g32p_row26_traceSegment_081_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 324 9 9, g32p_row26_traceSegment_081_0324_0009, g32p_row26_traceSegment_081_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 342 9 9, g32p_row26_traceSegment_081_0342_0009, g32p_row26_traceSegment_081_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 324 18 18, g32p_row26_traceSegment_081_0324_0018, g32p_row26_traceSegment_081_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 288 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 288 36 36, g32p_row26_traceSegment_081_0288_0036, g32p_row26_traceSegment_081_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 360 9 9, g32p_row26_traceSegment_081_0360_0009, g32p_row26_traceSegment_081_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 378 9 9, g32p_row26_traceSegment_081_0378_0009, g32p_row26_traceSegment_081_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 360 18 18, g32p_row26_traceSegment_081_0360_0018, g32p_row26_traceSegment_081_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 396 9 9, g32p_row26_traceSegment_081_0396_0009, g32p_row26_traceSegment_081_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 414 9 9, g32p_row26_traceSegment_081_0414_0009, g32p_row26_traceSegment_081_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 396 18 18, g32p_row26_traceSegment_081_0396_0018, g32p_row26_traceSegment_081_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 360 36 36, g32p_row26_traceSegment_081_0360_0036, g32p_row26_traceSegment_081_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_081 288 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 288 72 72, g32p_row26_traceSegment_081_0288_0072, g32p_row26_traceSegment_081_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 432 9 9, g32p_row26_traceSegment_081_0432_0009, g32p_row26_traceSegment_081_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 450 9 9, g32p_row26_traceSegment_081_0450_0009, g32p_row26_traceSegment_081_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 432 18 18, g32p_row26_traceSegment_081_0432_0018, g32p_row26_traceSegment_081_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 468 9 9, g32p_row26_traceSegment_081_0468_0009, g32p_row26_traceSegment_081_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 486 9 9, g32p_row26_traceSegment_081_0486_0009, g32p_row26_traceSegment_081_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 468 18 18, g32p_row26_traceSegment_081_0468_0018, g32p_row26_traceSegment_081_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 432 36 36, g32p_row26_traceSegment_081_0432_0036, g32p_row26_traceSegment_081_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 504 9 9, g32p_row26_traceSegment_081_0504_0009, g32p_row26_traceSegment_081_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 522 9 9, g32p_row26_traceSegment_081_0522_0009, g32p_row26_traceSegment_081_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 504 18 18, g32p_row26_traceSegment_081_0504_0018, g32p_row26_traceSegment_081_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 540 9 9, g32p_row26_traceSegment_081_0540_0009, g32p_row26_traceSegment_081_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_081 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_081_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_081 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 558 9 9, g32p_row26_traceSegment_081_0558_0009, g32p_row26_traceSegment_081_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_081 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 540 18 18, g32p_row26_traceSegment_081_0540_0018, g32p_row26_traceSegment_081_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_081 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 504 36 36, g32p_row26_traceSegment_081_0504_0036, g32p_row26_traceSegment_081_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_081 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 432 72 72, g32p_row26_traceSegment_081_0432_0072, g32p_row26_traceSegment_081_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_081 288 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 288 144 144, g32p_row26_traceSegment_081_0288_0144, g32p_row26_traceSegment_081_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_081_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_081 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_081 0 288 288, g32p_row26_traceSegment_081_0000_0288, g32p_row26_traceSegment_081_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_081_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_082_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 0 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 0 9 9, g32p_row26_traceSegment_082_0000_0009, g32p_row26_traceSegment_082_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 18 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 18 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 18 9 9, g32p_row26_traceSegment_082_0018_0009, g32p_row26_traceSegment_082_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 0 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 0 18 18, g32p_row26_traceSegment_082_0000_0018, g32p_row26_traceSegment_082_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 36 9 9, g32p_row26_traceSegment_082_0036_0009, g32p_row26_traceSegment_082_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 54 9 9, g32p_row26_traceSegment_082_0054_0009, g32p_row26_traceSegment_082_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 36 18 18, g32p_row26_traceSegment_082_0036_0018, g32p_row26_traceSegment_082_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 0 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 0 36 36, g32p_row26_traceSegment_082_0000_0036, g32p_row26_traceSegment_082_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 72 9 9, g32p_row26_traceSegment_082_0072_0009, g32p_row26_traceSegment_082_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 90 9 9, g32p_row26_traceSegment_082_0090_0009, g32p_row26_traceSegment_082_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 72 18 18, g32p_row26_traceSegment_082_0072_0018, g32p_row26_traceSegment_082_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 108 9 9, g32p_row26_traceSegment_082_0108_0009, g32p_row26_traceSegment_082_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 126 9 9, g32p_row26_traceSegment_082_0126_0009, g32p_row26_traceSegment_082_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 108 18 18, g32p_row26_traceSegment_082_0108_0018, g32p_row26_traceSegment_082_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 72 36 36, g32p_row26_traceSegment_082_0072_0036, g32p_row26_traceSegment_082_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_082 0 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 0 72 72, g32p_row26_traceSegment_082_0000_0072, g32p_row26_traceSegment_082_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 144 9 9, g32p_row26_traceSegment_082_0144_0009, g32p_row26_traceSegment_082_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 162 9 9, g32p_row26_traceSegment_082_0162_0009, g32p_row26_traceSegment_082_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 144 18 18, g32p_row26_traceSegment_082_0144_0018, g32p_row26_traceSegment_082_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 180 9 9, g32p_row26_traceSegment_082_0180_0009, g32p_row26_traceSegment_082_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 198 9 9, g32p_row26_traceSegment_082_0198_0009, g32p_row26_traceSegment_082_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 180 18 18, g32p_row26_traceSegment_082_0180_0018, g32p_row26_traceSegment_082_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 144 36 36, g32p_row26_traceSegment_082_0144_0036, g32p_row26_traceSegment_082_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 216 9 9, g32p_row26_traceSegment_082_0216_0009, g32p_row26_traceSegment_082_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 234 9 9, g32p_row26_traceSegment_082_0234_0009, g32p_row26_traceSegment_082_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 216 18 18, g32p_row26_traceSegment_082_0216_0018, g32p_row26_traceSegment_082_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 252 9 9, g32p_row26_traceSegment_082_0252_0009, g32p_row26_traceSegment_082_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 270 9 9, g32p_row26_traceSegment_082_0270_0009, g32p_row26_traceSegment_082_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 252 18 18, g32p_row26_traceSegment_082_0252_0018, g32p_row26_traceSegment_082_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 216 36 36, g32p_row26_traceSegment_082_0216_0036, g32p_row26_traceSegment_082_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_082 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 144 72 72, g32p_row26_traceSegment_082_0144_0072, g32p_row26_traceSegment_082_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_082 0 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 0 144 144, g32p_row26_traceSegment_082_0000_0144, g32p_row26_traceSegment_082_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 288 9 9, g32p_row26_traceSegment_082_0288_0009, g32p_row26_traceSegment_082_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 306 9 9, g32p_row26_traceSegment_082_0306_0009, g32p_row26_traceSegment_082_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 288 18 18, g32p_row26_traceSegment_082_0288_0018, g32p_row26_traceSegment_082_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 324 9 9, g32p_row26_traceSegment_082_0324_0009, g32p_row26_traceSegment_082_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 342 9 9, g32p_row26_traceSegment_082_0342_0009, g32p_row26_traceSegment_082_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 324 18 18, g32p_row26_traceSegment_082_0324_0018, g32p_row26_traceSegment_082_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 288 36 36, g32p_row26_traceSegment_082_0288_0036, g32p_row26_traceSegment_082_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 360 9 9, g32p_row26_traceSegment_082_0360_0009, g32p_row26_traceSegment_082_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 378 9 9, g32p_row26_traceSegment_082_0378_0009, g32p_row26_traceSegment_082_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 360 18 18, g32p_row26_traceSegment_082_0360_0018, g32p_row26_traceSegment_082_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 396 9 9, g32p_row26_traceSegment_082_0396_0009, g32p_row26_traceSegment_082_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 414 9 9, g32p_row26_traceSegment_082_0414_0009, g32p_row26_traceSegment_082_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 396 18 18, g32p_row26_traceSegment_082_0396_0018, g32p_row26_traceSegment_082_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 360 36 36, g32p_row26_traceSegment_082_0360_0036, g32p_row26_traceSegment_082_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_082 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 288 72 72, g32p_row26_traceSegment_082_0288_0072, g32p_row26_traceSegment_082_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 432 9 9, g32p_row26_traceSegment_082_0432_0009, g32p_row26_traceSegment_082_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 450 9 9, g32p_row26_traceSegment_082_0450_0009, g32p_row26_traceSegment_082_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 432 18 18, g32p_row26_traceSegment_082_0432_0018, g32p_row26_traceSegment_082_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 468 9 9, g32p_row26_traceSegment_082_0468_0009, g32p_row26_traceSegment_082_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 486 9 9, g32p_row26_traceSegment_082_0486_0009, g32p_row26_traceSegment_082_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 468 18 18, g32p_row26_traceSegment_082_0468_0018, g32p_row26_traceSegment_082_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 432 36 36, g32p_row26_traceSegment_082_0432_0036, g32p_row26_traceSegment_082_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 504 9 9, g32p_row26_traceSegment_082_0504_0009, g32p_row26_traceSegment_082_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 522 9 9, g32p_row26_traceSegment_082_0522_0009, g32p_row26_traceSegment_082_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 504 18 18, g32p_row26_traceSegment_082_0504_0018, g32p_row26_traceSegment_082_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 540 9 9, g32p_row26_traceSegment_082_0540_0009, g32p_row26_traceSegment_082_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_082 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_082_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_082 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 558 9 9, g32p_row26_traceSegment_082_0558_0009, g32p_row26_traceSegment_082_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_082 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 540 18 18, g32p_row26_traceSegment_082_0540_0018, g32p_row26_traceSegment_082_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_082 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 504 36 36, g32p_row26_traceSegment_082_0504_0036, g32p_row26_traceSegment_082_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_082 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 432 72 72, g32p_row26_traceSegment_082_0432_0072, g32p_row26_traceSegment_082_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_082 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 288 144 144, g32p_row26_traceSegment_082_0288_0144, g32p_row26_traceSegment_082_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_082_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_082 0 576 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_082 0 288 288, g32p_row26_traceSegment_082_0000_0288, g32p_row26_traceSegment_082_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 82 = [0, 0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_082_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_083 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 83 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_083_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 0 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 0 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 0 9 9, g32p_row26_traceSegment_083_0000_0009, g32p_row26_traceSegment_083_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 27 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 18 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 18 9 9, g32p_row26_traceSegment_083_0018_0009, g32p_row26_traceSegment_083_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 0 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 0 18 18, g32p_row26_traceSegment_083_0000_0018, g32p_row26_traceSegment_083_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 36 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 45 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 36 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 36 9 9, g32p_row26_traceSegment_083_0036_0009, g32p_row26_traceSegment_083_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 54 9 9, g32p_row26_traceSegment_083_0054_0009, g32p_row26_traceSegment_083_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 36 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 36 18 18, g32p_row26_traceSegment_083_0036_0018, g32p_row26_traceSegment_083_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 0 72 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 0 36 36, g32p_row26_traceSegment_083_0000_0036, g32p_row26_traceSegment_083_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 72 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 72 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 72 9 9, g32p_row26_traceSegment_083_0072_0009, g32p_row26_traceSegment_083_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 90 9 9, g32p_row26_traceSegment_083_0090_0009, g32p_row26_traceSegment_083_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 72 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 72 18 18, g32p_row26_traceSegment_083_0072_0018, g32p_row26_traceSegment_083_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 108 9 9, g32p_row26_traceSegment_083_0108_0009, g32p_row26_traceSegment_083_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 126 9 9, g32p_row26_traceSegment_083_0126_0009, g32p_row26_traceSegment_083_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 108 18 18, g32p_row26_traceSegment_083_0108_0018, g32p_row26_traceSegment_083_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 72 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 72 36 36, g32p_row26_traceSegment_083_0072_0036, g32p_row26_traceSegment_083_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_083 0 144 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 0 72 72, g32p_row26_traceSegment_083_0000_0072, g32p_row26_traceSegment_083_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 144 9 9, g32p_row26_traceSegment_083_0144_0009, g32p_row26_traceSegment_083_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 162 9 9, g32p_row26_traceSegment_083_0162_0009, g32p_row26_traceSegment_083_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 144 18 18, g32p_row26_traceSegment_083_0144_0018, g32p_row26_traceSegment_083_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 180 9 9, g32p_row26_traceSegment_083_0180_0009, g32p_row26_traceSegment_083_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 207 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 198 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 198 9 9, g32p_row26_traceSegment_083_0198_0009, g32p_row26_traceSegment_083_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 180 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 180 18 18, g32p_row26_traceSegment_083_0180_0018, g32p_row26_traceSegment_083_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 144 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 144 36 36, g32p_row26_traceSegment_083_0144_0036, g32p_row26_traceSegment_083_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 216 9 9, g32p_row26_traceSegment_083_0216_0009, g32p_row26_traceSegment_083_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 234 9 9, g32p_row26_traceSegment_083_0234_0009, g32p_row26_traceSegment_083_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 216 18 18, g32p_row26_traceSegment_083_0216_0018, g32p_row26_traceSegment_083_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 252 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 252 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 252 9 9, g32p_row26_traceSegment_083_0252_0009, g32p_row26_traceSegment_083_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 270 9 9, g32p_row26_traceSegment_083_0270_0009, g32p_row26_traceSegment_083_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 252 18 18, g32p_row26_traceSegment_083_0252_0018, g32p_row26_traceSegment_083_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 216 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 216 36 36, g32p_row26_traceSegment_083_0216_0036, g32p_row26_traceSegment_083_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_083 144 144 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 144 72 72, g32p_row26_traceSegment_083_0144_0072, g32p_row26_traceSegment_083_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_083 0 288 = [0, 0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 0 144 144, g32p_row26_traceSegment_083_0000_0144, g32p_row26_traceSegment_083_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 288 9 9, g32p_row26_traceSegment_083_0288_0009, g32p_row26_traceSegment_083_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 306 9 9, g32p_row26_traceSegment_083_0306_0009, g32p_row26_traceSegment_083_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 288 18 18, g32p_row26_traceSegment_083_0288_0018, g32p_row26_traceSegment_083_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 324 9 9, g32p_row26_traceSegment_083_0324_0009, g32p_row26_traceSegment_083_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 342 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 351 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 342 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 342 9 9, g32p_row26_traceSegment_083_0342_0009, g32p_row26_traceSegment_083_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 324 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 324 18 18, g32p_row26_traceSegment_083_0324_0018, g32p_row26_traceSegment_083_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 288 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 288 36 36, g32p_row26_traceSegment_083_0288_0036, g32p_row26_traceSegment_083_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 369 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 360 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 360 9 9, g32p_row26_traceSegment_083_0360_0009, g32p_row26_traceSegment_083_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 378 9 9, g32p_row26_traceSegment_083_0378_0009, g32p_row26_traceSegment_083_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 360 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 360 18 18, g32p_row26_traceSegment_083_0360_0018, g32p_row26_traceSegment_083_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 405 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 396 9 9, g32p_row26_traceSegment_083_0396_0009, g32p_row26_traceSegment_083_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 414 9 9, g32p_row26_traceSegment_083_0414_0009, g32p_row26_traceSegment_083_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 396 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 396 18 18, g32p_row26_traceSegment_083_0396_0018, g32p_row26_traceSegment_083_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 360 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 360 36 36, g32p_row26_traceSegment_083_0360_0036, g32p_row26_traceSegment_083_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_083 288 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 288 72 72, g32p_row26_traceSegment_083_0288_0072, g32p_row26_traceSegment_083_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 432 9 9, g32p_row26_traceSegment_083_0432_0009, g32p_row26_traceSegment_083_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 450 9 9, g32p_row26_traceSegment_083_0450_0009, g32p_row26_traceSegment_083_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 432 18 18, g32p_row26_traceSegment_083_0432_0018, g32p_row26_traceSegment_083_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 468 9 9, g32p_row26_traceSegment_083_0468_0009, g32p_row26_traceSegment_083_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 486 9 9, g32p_row26_traceSegment_083_0486_0009, g32p_row26_traceSegment_083_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 468 18 18, g32p_row26_traceSegment_083_0468_0018, g32p_row26_traceSegment_083_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 432 36 36, g32p_row26_traceSegment_083_0432_0036, g32p_row26_traceSegment_083_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 504 9 9, g32p_row26_traceSegment_083_0504_0009, g32p_row26_traceSegment_083_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 522 9 9, g32p_row26_traceSegment_083_0522_0009, g32p_row26_traceSegment_083_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 504 18 18, g32p_row26_traceSegment_083_0504_0018, g32p_row26_traceSegment_083_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 540 9 9, g32p_row26_traceSegment_083_0540_0009, g32p_row26_traceSegment_083_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_083 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_083_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_083 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 558 9 9, g32p_row26_traceSegment_083_0558_0009, g32p_row26_traceSegment_083_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_083 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 540 18 18, g32p_row26_traceSegment_083_0540_0018, g32p_row26_traceSegment_083_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_083 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 504 36 36, g32p_row26_traceSegment_083_0504_0036, g32p_row26_traceSegment_083_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_083 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 432 72 72, g32p_row26_traceSegment_083_0432_0072, g32p_row26_traceSegment_083_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_083 288 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 288 144 144, g32p_row26_traceSegment_083_0288_0144, g32p_row26_traceSegment_083_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_083_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_083 0 576 = [0, 0, 8, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_083 0 288 288, g32p_row26_traceSegment_083_0000_0288, g32p_row26_traceSegment_083_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 83 = [0, 0, 8, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_083_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_085 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 85 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_085_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 9 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 0 9 9, g32p_row26_traceSegment_085_0000_0009, g32p_row26_traceSegment_085_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 18 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 18 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 18 9 9, g32p_row26_traceSegment_085_0018_0009, g32p_row26_traceSegment_085_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 0 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 0 18 18, g32p_row26_traceSegment_085_0000_0018, g32p_row26_traceSegment_085_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 36 9 9, g32p_row26_traceSegment_085_0036_0009, g32p_row26_traceSegment_085_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 54 9 9, g32p_row26_traceSegment_085_0054_0009, g32p_row26_traceSegment_085_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 36 18 18, g32p_row26_traceSegment_085_0036_0018, g32p_row26_traceSegment_085_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 0 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 0 36 36, g32p_row26_traceSegment_085_0000_0036, g32p_row26_traceSegment_085_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 72 9 9, g32p_row26_traceSegment_085_0072_0009, g32p_row26_traceSegment_085_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 90 9 9, g32p_row26_traceSegment_085_0090_0009, g32p_row26_traceSegment_085_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 72 18 18, g32p_row26_traceSegment_085_0072_0018, g32p_row26_traceSegment_085_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 108 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 108 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 108 9 9, g32p_row26_traceSegment_085_0108_0009, g32p_row26_traceSegment_085_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 126 9 9, g32p_row26_traceSegment_085_0126_0009, g32p_row26_traceSegment_085_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 108 18 18, g32p_row26_traceSegment_085_0108_0018, g32p_row26_traceSegment_085_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 72 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 72 36 36, g32p_row26_traceSegment_085_0072_0036, g32p_row26_traceSegment_085_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_085 0 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 0 72 72, g32p_row26_traceSegment_085_0000_0072, g32p_row26_traceSegment_085_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 144 9 9, g32p_row26_traceSegment_085_0144_0009, g32p_row26_traceSegment_085_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 162 9 9, g32p_row26_traceSegment_085_0162_0009, g32p_row26_traceSegment_085_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 144 18 18, g32p_row26_traceSegment_085_0144_0018, g32p_row26_traceSegment_085_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 180 9 9, g32p_row26_traceSegment_085_0180_0009, g32p_row26_traceSegment_085_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 198 9 9, g32p_row26_traceSegment_085_0198_0009, g32p_row26_traceSegment_085_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 180 18 18, g32p_row26_traceSegment_085_0180_0018, g32p_row26_traceSegment_085_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 144 36 36, g32p_row26_traceSegment_085_0144_0036, g32p_row26_traceSegment_085_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 216 9 9, g32p_row26_traceSegment_085_0216_0009, g32p_row26_traceSegment_085_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 234 9 9, g32p_row26_traceSegment_085_0234_0009, g32p_row26_traceSegment_085_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 216 18 18, g32p_row26_traceSegment_085_0216_0018, g32p_row26_traceSegment_085_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 252 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 252 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 252 9 9, g32p_row26_traceSegment_085_0252_0009, g32p_row26_traceSegment_085_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 270 9 9, g32p_row26_traceSegment_085_0270_0009, g32p_row26_traceSegment_085_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 252 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 252 18 18, g32p_row26_traceSegment_085_0252_0018, g32p_row26_traceSegment_085_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 216 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 216 36 36, g32p_row26_traceSegment_085_0216_0036, g32p_row26_traceSegment_085_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_085 144 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 144 72 72, g32p_row26_traceSegment_085_0144_0072, g32p_row26_traceSegment_085_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_085 0 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 0 144 144, g32p_row26_traceSegment_085_0000_0144, g32p_row26_traceSegment_085_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 288 9 9, g32p_row26_traceSegment_085_0288_0009, g32p_row26_traceSegment_085_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 306 9 9, g32p_row26_traceSegment_085_0306_0009, g32p_row26_traceSegment_085_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 288 18 18, g32p_row26_traceSegment_085_0288_0018, g32p_row26_traceSegment_085_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 324 9 9, g32p_row26_traceSegment_085_0324_0009, g32p_row26_traceSegment_085_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 342 9 9, g32p_row26_traceSegment_085_0342_0009, g32p_row26_traceSegment_085_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 324 18 18, g32p_row26_traceSegment_085_0324_0018, g32p_row26_traceSegment_085_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 288 36 36, g32p_row26_traceSegment_085_0288_0036, g32p_row26_traceSegment_085_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 360 9 9, g32p_row26_traceSegment_085_0360_0009, g32p_row26_traceSegment_085_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 378 9 9, g32p_row26_traceSegment_085_0378_0009, g32p_row26_traceSegment_085_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 360 18 18, g32p_row26_traceSegment_085_0360_0018, g32p_row26_traceSegment_085_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 396 9 9, g32p_row26_traceSegment_085_0396_0009, g32p_row26_traceSegment_085_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 414 9 9, g32p_row26_traceSegment_085_0414_0009, g32p_row26_traceSegment_085_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 396 18 18, g32p_row26_traceSegment_085_0396_0018, g32p_row26_traceSegment_085_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 360 36 36, g32p_row26_traceSegment_085_0360_0036, g32p_row26_traceSegment_085_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_085 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 288 72 72, g32p_row26_traceSegment_085_0288_0072, g32p_row26_traceSegment_085_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 432 9 9, g32p_row26_traceSegment_085_0432_0009, g32p_row26_traceSegment_085_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 450 9 9, g32p_row26_traceSegment_085_0450_0009, g32p_row26_traceSegment_085_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 432 18 18, g32p_row26_traceSegment_085_0432_0018, g32p_row26_traceSegment_085_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 468 9 9, g32p_row26_traceSegment_085_0468_0009, g32p_row26_traceSegment_085_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 486 9 9, g32p_row26_traceSegment_085_0486_0009, g32p_row26_traceSegment_085_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 468 18 18, g32p_row26_traceSegment_085_0468_0018, g32p_row26_traceSegment_085_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 432 36 36, g32p_row26_traceSegment_085_0432_0036, g32p_row26_traceSegment_085_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 504 9 9, g32p_row26_traceSegment_085_0504_0009, g32p_row26_traceSegment_085_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 522 9 9, g32p_row26_traceSegment_085_0522_0009, g32p_row26_traceSegment_085_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 504 18 18, g32p_row26_traceSegment_085_0504_0018, g32p_row26_traceSegment_085_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 540 9 9, g32p_row26_traceSegment_085_0540_0009, g32p_row26_traceSegment_085_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_085 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_085_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_085 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 558 9 9, g32p_row26_traceSegment_085_0558_0009, g32p_row26_traceSegment_085_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_085 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 540 18 18, g32p_row26_traceSegment_085_0540_0018, g32p_row26_traceSegment_085_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_085 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 504 36 36, g32p_row26_traceSegment_085_0504_0036, g32p_row26_traceSegment_085_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_085 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 432 72 72, g32p_row26_traceSegment_085_0432_0072, g32p_row26_traceSegment_085_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_085 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 288 144 144, g32p_row26_traceSegment_085_0288_0144, g32p_row26_traceSegment_085_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_085_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_085 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_085 0 288 288, g32p_row26_traceSegment_085_0000_0288, g32p_row26_traceSegment_085_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 85 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_085_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 76) (g32p_literalTraceValue 25 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_076]
  decide +kernel

theorem g32p_row26_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 77) (g32p_literalTraceValue 25 77)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_077]
  decide +kernel

theorem g32p_row26_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 79) (g32p_literalTraceValue 25 79)
      [1, -1, 1] [1728, 1728, 1728] = true := by
  rw [g32p_row26_traceCoefficients_079]
  decide +kernel

theorem g32p_row26_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 80) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 80) (g32p_literalTraceValue 25 80)
      [1, -1, 1] [-576, 576, 576] = true := by
  rw [g32p_row26_traceCoefficients_080]
  decide +kernel

theorem g32p_row26_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 81) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 81) (g32p_literalTraceValue 25 81)
      [1, -1, 1] [1728, 1728, 1728] = true := by
  rw [g32p_row26_traceCoefficients_081]
  decide +kernel

theorem g32p_row26_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 82) (g32p_literalTraceValue 25 82)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_082]
  decide +kernel

theorem g32p_row26_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 83) (g32p_literalTraceValue 25 83)
      [1, -1, 1] [0, 0, 1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_083]
  decide +kernel

theorem g32p_row26_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 85) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 85) (g32p_literalTraceValue 25 85)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_085]
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

private def g32p_row26_traceSegment_087 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 87 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_087_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 0 9 9, g32p_row26_traceSegment_087_0000_0009, g32p_row26_traceSegment_087_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 18 9 9, g32p_row26_traceSegment_087_0018_0009, g32p_row26_traceSegment_087_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 0 18 18, g32p_row26_traceSegment_087_0000_0018, g32p_row26_traceSegment_087_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 36 9 9, g32p_row26_traceSegment_087_0036_0009, g32p_row26_traceSegment_087_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 54 9 9, g32p_row26_traceSegment_087_0054_0009, g32p_row26_traceSegment_087_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 36 18 18, g32p_row26_traceSegment_087_0036_0018, g32p_row26_traceSegment_087_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 0 36 36, g32p_row26_traceSegment_087_0000_0036, g32p_row26_traceSegment_087_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 72 9 9, g32p_row26_traceSegment_087_0072_0009, g32p_row26_traceSegment_087_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 90 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 90 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 90 9 9, g32p_row26_traceSegment_087_0090_0009, g32p_row26_traceSegment_087_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 72 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 72 18 18, g32p_row26_traceSegment_087_0072_0018, g32p_row26_traceSegment_087_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 108 9 9, g32p_row26_traceSegment_087_0108_0009, g32p_row26_traceSegment_087_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 126 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 126 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 126 9 9, g32p_row26_traceSegment_087_0126_0009, g32p_row26_traceSegment_087_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 108 18 18, g32p_row26_traceSegment_087_0108_0018, g32p_row26_traceSegment_087_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 72 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 72 36 36, g32p_row26_traceSegment_087_0072_0036, g32p_row26_traceSegment_087_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_087 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 0 72 72, g32p_row26_traceSegment_087_0000_0072, g32p_row26_traceSegment_087_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 144 9 9, g32p_row26_traceSegment_087_0144_0009, g32p_row26_traceSegment_087_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 162 9 9, g32p_row26_traceSegment_087_0162_0009, g32p_row26_traceSegment_087_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 144 18 18, g32p_row26_traceSegment_087_0144_0018, g32p_row26_traceSegment_087_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 180 9 9, g32p_row26_traceSegment_087_0180_0009, g32p_row26_traceSegment_087_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 198 9 9, g32p_row26_traceSegment_087_0198_0009, g32p_row26_traceSegment_087_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 180 18 18, g32p_row26_traceSegment_087_0180_0018, g32p_row26_traceSegment_087_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 144 36 36, g32p_row26_traceSegment_087_0144_0036, g32p_row26_traceSegment_087_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 216 9 9, g32p_row26_traceSegment_087_0216_0009, g32p_row26_traceSegment_087_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 234 9 9, g32p_row26_traceSegment_087_0234_0009, g32p_row26_traceSegment_087_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 216 18 18, g32p_row26_traceSegment_087_0216_0018, g32p_row26_traceSegment_087_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 252 9 9, g32p_row26_traceSegment_087_0252_0009, g32p_row26_traceSegment_087_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 270 9 9, g32p_row26_traceSegment_087_0270_0009, g32p_row26_traceSegment_087_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 252 18 18, g32p_row26_traceSegment_087_0252_0018, g32p_row26_traceSegment_087_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 216 36 36, g32p_row26_traceSegment_087_0216_0036, g32p_row26_traceSegment_087_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_087 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 144 72 72, g32p_row26_traceSegment_087_0144_0072, g32p_row26_traceSegment_087_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_087 0 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 0 144 144, g32p_row26_traceSegment_087_0000_0144, g32p_row26_traceSegment_087_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 288 9 9, g32p_row26_traceSegment_087_0288_0009, g32p_row26_traceSegment_087_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 306 9 9, g32p_row26_traceSegment_087_0306_0009, g32p_row26_traceSegment_087_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 288 18 18, g32p_row26_traceSegment_087_0288_0018, g32p_row26_traceSegment_087_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 324 9 9, g32p_row26_traceSegment_087_0324_0009, g32p_row26_traceSegment_087_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 351 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 342 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 342 9 9, g32p_row26_traceSegment_087_0342_0009, g32p_row26_traceSegment_087_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 324 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 324 18 18, g32p_row26_traceSegment_087_0324_0018, g32p_row26_traceSegment_087_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 288 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 288 36 36, g32p_row26_traceSegment_087_0288_0036, g32p_row26_traceSegment_087_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 360 9 9, g32p_row26_traceSegment_087_0360_0009, g32p_row26_traceSegment_087_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 378 9 9, g32p_row26_traceSegment_087_0378_0009, g32p_row26_traceSegment_087_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 360 18 18, g32p_row26_traceSegment_087_0360_0018, g32p_row26_traceSegment_087_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 396 9 9, g32p_row26_traceSegment_087_0396_0009, g32p_row26_traceSegment_087_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 414 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 414 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 414 9 9, g32p_row26_traceSegment_087_0414_0009, g32p_row26_traceSegment_087_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 396 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 396 18 18, g32p_row26_traceSegment_087_0396_0018, g32p_row26_traceSegment_087_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 360 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 360 36 36, g32p_row26_traceSegment_087_0360_0036, g32p_row26_traceSegment_087_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_087 288 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 288 72 72, g32p_row26_traceSegment_087_0288_0072, g32p_row26_traceSegment_087_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 432 9 9, g32p_row26_traceSegment_087_0432_0009, g32p_row26_traceSegment_087_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 450 9 9, g32p_row26_traceSegment_087_0450_0009, g32p_row26_traceSegment_087_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 432 18 18, g32p_row26_traceSegment_087_0432_0018, g32p_row26_traceSegment_087_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 468 9 9, g32p_row26_traceSegment_087_0468_0009, g32p_row26_traceSegment_087_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 486 9 9, g32p_row26_traceSegment_087_0486_0009, g32p_row26_traceSegment_087_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 468 18 18, g32p_row26_traceSegment_087_0468_0018, g32p_row26_traceSegment_087_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 432 36 36, g32p_row26_traceSegment_087_0432_0036, g32p_row26_traceSegment_087_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 504 9 9, g32p_row26_traceSegment_087_0504_0009, g32p_row26_traceSegment_087_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 522 9 9, g32p_row26_traceSegment_087_0522_0009, g32p_row26_traceSegment_087_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 504 18 18, g32p_row26_traceSegment_087_0504_0018, g32p_row26_traceSegment_087_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 540 9 9, g32p_row26_traceSegment_087_0540_0009, g32p_row26_traceSegment_087_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_087 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_087_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_087 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 558 9 9, g32p_row26_traceSegment_087_0558_0009, g32p_row26_traceSegment_087_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_087 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 540 18 18, g32p_row26_traceSegment_087_0540_0018, g32p_row26_traceSegment_087_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_087 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 504 36 36, g32p_row26_traceSegment_087_0504_0036, g32p_row26_traceSegment_087_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_087 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 432 72 72, g32p_row26_traceSegment_087_0432_0072, g32p_row26_traceSegment_087_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_087 288 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 288 144 144, g32p_row26_traceSegment_087_0288_0144, g32p_row26_traceSegment_087_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_087_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_087 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_087 0 288 288, g32p_row26_traceSegment_087_0000_0288, g32p_row26_traceSegment_087_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 87 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_087_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_088 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 88 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_088_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 0 9 9, g32p_row26_traceSegment_088_0000_0009, g32p_row26_traceSegment_088_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 18 9 9, g32p_row26_traceSegment_088_0018_0009, g32p_row26_traceSegment_088_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 0 18 18, g32p_row26_traceSegment_088_0000_0018, g32p_row26_traceSegment_088_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 36 9 9, g32p_row26_traceSegment_088_0036_0009, g32p_row26_traceSegment_088_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 54 9 9, g32p_row26_traceSegment_088_0054_0009, g32p_row26_traceSegment_088_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 36 18 18, g32p_row26_traceSegment_088_0036_0018, g32p_row26_traceSegment_088_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 0 36 36, g32p_row26_traceSegment_088_0000_0036, g32p_row26_traceSegment_088_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 72 9 9, g32p_row26_traceSegment_088_0072_0009, g32p_row26_traceSegment_088_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 90 9 9, g32p_row26_traceSegment_088_0090_0009, g32p_row26_traceSegment_088_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 72 18 18, g32p_row26_traceSegment_088_0072_0018, g32p_row26_traceSegment_088_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 108 9 9, g32p_row26_traceSegment_088_0108_0009, g32p_row26_traceSegment_088_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 126 9 9, g32p_row26_traceSegment_088_0126_0009, g32p_row26_traceSegment_088_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 108 18 18, g32p_row26_traceSegment_088_0108_0018, g32p_row26_traceSegment_088_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 72 36 36, g32p_row26_traceSegment_088_0072_0036, g32p_row26_traceSegment_088_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_088 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 0 72 72, g32p_row26_traceSegment_088_0000_0072, g32p_row26_traceSegment_088_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 144 9 9, g32p_row26_traceSegment_088_0144_0009, g32p_row26_traceSegment_088_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 162 9 9, g32p_row26_traceSegment_088_0162_0009, g32p_row26_traceSegment_088_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 144 18 18, g32p_row26_traceSegment_088_0144_0018, g32p_row26_traceSegment_088_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 180 9 9, g32p_row26_traceSegment_088_0180_0009, g32p_row26_traceSegment_088_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 198 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 198 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 198 9 9, g32p_row26_traceSegment_088_0198_0009, g32p_row26_traceSegment_088_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 180 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 180 18 18, g32p_row26_traceSegment_088_0180_0018, g32p_row26_traceSegment_088_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 144 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 144 36 36, g32p_row26_traceSegment_088_0144_0036, g32p_row26_traceSegment_088_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 216 9 9, g32p_row26_traceSegment_088_0216_0009, g32p_row26_traceSegment_088_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 234 9 9, g32p_row26_traceSegment_088_0234_0009, g32p_row26_traceSegment_088_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 216 18 18, g32p_row26_traceSegment_088_0216_0018, g32p_row26_traceSegment_088_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 252 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 252 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 252 9 9, g32p_row26_traceSegment_088_0252_0009, g32p_row26_traceSegment_088_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 270 9 9, g32p_row26_traceSegment_088_0270_0009, g32p_row26_traceSegment_088_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 252 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 252 18 18, g32p_row26_traceSegment_088_0252_0018, g32p_row26_traceSegment_088_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 216 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 216 36 36, g32p_row26_traceSegment_088_0216_0036, g32p_row26_traceSegment_088_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_088 144 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 144 72 72, g32p_row26_traceSegment_088_0144_0072, g32p_row26_traceSegment_088_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_088 0 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 0 144 144, g32p_row26_traceSegment_088_0000_0144, g32p_row26_traceSegment_088_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 288 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 288 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 288 9 9, g32p_row26_traceSegment_088_0288_0009, g32p_row26_traceSegment_088_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 306 9 9, g32p_row26_traceSegment_088_0306_0009, g32p_row26_traceSegment_088_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 288 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 288 18 18, g32p_row26_traceSegment_088_0288_0018, g32p_row26_traceSegment_088_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 324 9 9, g32p_row26_traceSegment_088_0324_0009, g32p_row26_traceSegment_088_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 342 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 342 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 342 9 9, g32p_row26_traceSegment_088_0342_0009, g32p_row26_traceSegment_088_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 324 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 324 18 18, g32p_row26_traceSegment_088_0324_0018, g32p_row26_traceSegment_088_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 288 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 288 36 36, g32p_row26_traceSegment_088_0288_0036, g32p_row26_traceSegment_088_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 360 9 9, g32p_row26_traceSegment_088_0360_0009, g32p_row26_traceSegment_088_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 378 9 9, g32p_row26_traceSegment_088_0378_0009, g32p_row26_traceSegment_088_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 360 18 18, g32p_row26_traceSegment_088_0360_0018, g32p_row26_traceSegment_088_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 396 9 9, g32p_row26_traceSegment_088_0396_0009, g32p_row26_traceSegment_088_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 414 9 9, g32p_row26_traceSegment_088_0414_0009, g32p_row26_traceSegment_088_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 396 18 18, g32p_row26_traceSegment_088_0396_0018, g32p_row26_traceSegment_088_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 360 36 36, g32p_row26_traceSegment_088_0360_0036, g32p_row26_traceSegment_088_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_088 288 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 288 72 72, g32p_row26_traceSegment_088_0288_0072, g32p_row26_traceSegment_088_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 432 9 9, g32p_row26_traceSegment_088_0432_0009, g32p_row26_traceSegment_088_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 450 9 9, g32p_row26_traceSegment_088_0450_0009, g32p_row26_traceSegment_088_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 432 18 18, g32p_row26_traceSegment_088_0432_0018, g32p_row26_traceSegment_088_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 468 9 9, g32p_row26_traceSegment_088_0468_0009, g32p_row26_traceSegment_088_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 486 9 9, g32p_row26_traceSegment_088_0486_0009, g32p_row26_traceSegment_088_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 468 18 18, g32p_row26_traceSegment_088_0468_0018, g32p_row26_traceSegment_088_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 432 36 36, g32p_row26_traceSegment_088_0432_0036, g32p_row26_traceSegment_088_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 504 9 9, g32p_row26_traceSegment_088_0504_0009, g32p_row26_traceSegment_088_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 522 9 9, g32p_row26_traceSegment_088_0522_0009, g32p_row26_traceSegment_088_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 504 18 18, g32p_row26_traceSegment_088_0504_0018, g32p_row26_traceSegment_088_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 540 9 9, g32p_row26_traceSegment_088_0540_0009, g32p_row26_traceSegment_088_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_088 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_088_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_088 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 558 9 9, g32p_row26_traceSegment_088_0558_0009, g32p_row26_traceSegment_088_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_088 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 540 18 18, g32p_row26_traceSegment_088_0540_0018, g32p_row26_traceSegment_088_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_088 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 504 36 36, g32p_row26_traceSegment_088_0504_0036, g32p_row26_traceSegment_088_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_088 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 432 72 72, g32p_row26_traceSegment_088_0432_0072, g32p_row26_traceSegment_088_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_088 288 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 288 144 144, g32p_row26_traceSegment_088_0288_0144, g32p_row26_traceSegment_088_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_088_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_088 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_088 0 288 288, g32p_row26_traceSegment_088_0000_0288, g32p_row26_traceSegment_088_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 88 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_088_0000_0576

end HodgeLean.Foundations.Program

end
end
