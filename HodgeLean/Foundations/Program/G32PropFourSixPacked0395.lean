import HodgeLean.Foundations.Program.G32PropFourSixPacked0393
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0394

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_049_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 9 9, g32p_row24_traceSegment_049_0000_0009, g32p_row24_traceSegment_049_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 18 9 9, g32p_row24_traceSegment_049_0018_0009, g32p_row24_traceSegment_049_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 18 18, g32p_row24_traceSegment_049_0000_0018, g32p_row24_traceSegment_049_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 36 9 9, g32p_row24_traceSegment_049_0036_0009, g32p_row24_traceSegment_049_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 54 9 9, g32p_row24_traceSegment_049_0054_0009, g32p_row24_traceSegment_049_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 36 18 18, g32p_row24_traceSegment_049_0036_0018, g32p_row24_traceSegment_049_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 36 36, g32p_row24_traceSegment_049_0000_0036, g32p_row24_traceSegment_049_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 72 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 81 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 72 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 72 9 9, g32p_row24_traceSegment_049_0072_0009, g32p_row24_traceSegment_049_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 90 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 99 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 90 18 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 90 9 9, g32p_row24_traceSegment_049_0090_0009, g32p_row24_traceSegment_049_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 72 36 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 72 18 18, g32p_row24_traceSegment_049_0072_0018, g32p_row24_traceSegment_049_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 117 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 108 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 108 9 9, g32p_row24_traceSegment_049_0108_0009, g32p_row24_traceSegment_049_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 126 9 9, g32p_row24_traceSegment_049_0126_0009, g32p_row24_traceSegment_049_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 108 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 108 18 18, g32p_row24_traceSegment_049_0108_0018, g32p_row24_traceSegment_049_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 72 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 72 36 36, g32p_row24_traceSegment_049_0072_0036, g32p_row24_traceSegment_049_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 0 144 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 72 72, g32p_row24_traceSegment_049_0000_0072, g32p_row24_traceSegment_049_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 153 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 144 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 144 9 9, g32p_row24_traceSegment_049_0144_0009, g32p_row24_traceSegment_049_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 162 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 162 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 162 9 9, g32p_row24_traceSegment_049_0162_0009, g32p_row24_traceSegment_049_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 144 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 144 18 18, g32p_row24_traceSegment_049_0144_0018, g32p_row24_traceSegment_049_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 180 9 9, g32p_row24_traceSegment_049_0180_0009, g32p_row24_traceSegment_049_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 198 9 9, g32p_row24_traceSegment_049_0198_0009, g32p_row24_traceSegment_049_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 180 18 18, g32p_row24_traceSegment_049_0180_0018, g32p_row24_traceSegment_049_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 144 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 144 36 36, g32p_row24_traceSegment_049_0144_0036, g32p_row24_traceSegment_049_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 216 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 216 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 216 9 9, g32p_row24_traceSegment_049_0216_0009, g32p_row24_traceSegment_049_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 234 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 243 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 234 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 234 9 9, g32p_row24_traceSegment_049_0234_0009, g32p_row24_traceSegment_049_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 216 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 216 18 18, g32p_row24_traceSegment_049_0216_0018, g32p_row24_traceSegment_049_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 261 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 252 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 252 9 9, g32p_row24_traceSegment_049_0252_0009, g32p_row24_traceSegment_049_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 270 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 279 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 270 18 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 270 9 9, g32p_row24_traceSegment_049_0270_0009, g32p_row24_traceSegment_049_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 252 36 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 252 18 18, g32p_row24_traceSegment_049_0252_0018, g32p_row24_traceSegment_049_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 216 72 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 216 36 36, g32p_row24_traceSegment_049_0216_0036, g32p_row24_traceSegment_049_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 144 144 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 144 72 72, g32p_row24_traceSegment_049_0144_0072, g32p_row24_traceSegment_049_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_049 0 288 = [0, 0, 0, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 144 144, g32p_row24_traceSegment_049_0000_0144, g32p_row24_traceSegment_049_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 288 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 297 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 288 18 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 288 9 9, g32p_row24_traceSegment_049_0288_0009, g32p_row24_traceSegment_049_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 315 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 306 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 306 9 9, g32p_row24_traceSegment_049_0306_0009, g32p_row24_traceSegment_049_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 288 36 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 288 18 18, g32p_row24_traceSegment_049_0288_0018, g32p_row24_traceSegment_049_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 324 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 324 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 324 9 9, g32p_row24_traceSegment_049_0324_0009, g32p_row24_traceSegment_049_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 342 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 342 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 342 9 9, g32p_row24_traceSegment_049_0342_0009, g32p_row24_traceSegment_049_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 324 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 324 18 18, g32p_row24_traceSegment_049_0324_0018, g32p_row24_traceSegment_049_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 288 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 288 36 36, g32p_row24_traceSegment_049_0288_0036, g32p_row24_traceSegment_049_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 369 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 360 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 360 9 9, g32p_row24_traceSegment_049_0360_0009, g32p_row24_traceSegment_049_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 378 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 387 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 378 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 378 9 9, g32p_row24_traceSegment_049_0378_0009, g32p_row24_traceSegment_049_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 360 36 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 360 18 18, g32p_row24_traceSegment_049_0360_0018, g32p_row24_traceSegment_049_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 396 9 9, g32p_row24_traceSegment_049_0396_0009, g32p_row24_traceSegment_049_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 414 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 423 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 414 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 414 9 9, g32p_row24_traceSegment_049_0414_0009, g32p_row24_traceSegment_049_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 396 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 396 18 18, g32p_row24_traceSegment_049_0396_0018, g32p_row24_traceSegment_049_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 360 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 360 36 36, g32p_row24_traceSegment_049_0360_0036, g32p_row24_traceSegment_049_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 288 144 = [0, 0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 288 72 72, g32p_row24_traceSegment_049_0288_0072, g32p_row24_traceSegment_049_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 432 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 432 9 9, g32p_row24_traceSegment_049_0432_0009, g32p_row24_traceSegment_049_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 450 9 9, g32p_row24_traceSegment_049_0450_0009, g32p_row24_traceSegment_049_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 432 18 18, g32p_row24_traceSegment_049_0432_0018, g32p_row24_traceSegment_049_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 477 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 468 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 468 9 9, g32p_row24_traceSegment_049_0468_0009, g32p_row24_traceSegment_049_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 486 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 486 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 486 9 9, g32p_row24_traceSegment_049_0486_0009, g32p_row24_traceSegment_049_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 468 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 468 18 18, g32p_row24_traceSegment_049_0468_0018, g32p_row24_traceSegment_049_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 432 72 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 432 36 36, g32p_row24_traceSegment_049_0432_0036, g32p_row24_traceSegment_049_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 504 9 9, g32p_row24_traceSegment_049_0504_0009, g32p_row24_traceSegment_049_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 531 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 522 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 522 9 9, g32p_row24_traceSegment_049_0522_0009, g32p_row24_traceSegment_049_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 504 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 504 18 18, g32p_row24_traceSegment_049_0504_0018, g32p_row24_traceSegment_049_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 540 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 540 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 540 9 9, g32p_row24_traceSegment_049_0540_0009, g32p_row24_traceSegment_049_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 558 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 567 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 558 18 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 558 9 9, g32p_row24_traceSegment_049_0558_0009, g32p_row24_traceSegment_049_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 540 36 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 540 18 18, g32p_row24_traceSegment_049_0540_0018, g32p_row24_traceSegment_049_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 504 72 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 504 36 36, g32p_row24_traceSegment_049_0504_0036, g32p_row24_traceSegment_049_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 432 144 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 432 72 72, g32p_row24_traceSegment_049_0432_0072, g32p_row24_traceSegment_049_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_049 288 288 = [0, 0, 0, 0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 288 144 144, g32p_row24_traceSegment_049_0288_0144, g32p_row24_traceSegment_049_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_049 0 576 = [0, 0, 0, 0, 0, 58] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 288 288, g32p_row24_traceSegment_049_0000_0288, g32p_row24_traceSegment_049_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 576 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 585 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 576 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 576 9 9, g32p_row24_traceSegment_049_0576_0009, g32p_row24_traceSegment_049_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 594 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 603 9 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 594 18 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 594 9 9, g32p_row24_traceSegment_049_0594_0009, g32p_row24_traceSegment_049_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 576 36 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 576 18 18, g32p_row24_traceSegment_049_0576_0018, g32p_row24_traceSegment_049_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 612 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 621 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 612 18 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 612 9 9, g32p_row24_traceSegment_049_0612_0009, g32p_row24_traceSegment_049_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 630 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 639 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 630 18 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 630 9 9, g32p_row24_traceSegment_049_0630_0009, g32p_row24_traceSegment_049_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 612 36 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 612 18 18, g32p_row24_traceSegment_049_0612_0018, g32p_row24_traceSegment_049_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 576 72 = [0, 0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 576 36 36, g32p_row24_traceSegment_049_0576_0036, g32p_row24_traceSegment_049_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 648 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 657 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 648 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 648 9 9, g32p_row24_traceSegment_049_0648_0009, g32p_row24_traceSegment_049_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 675 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 666 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 666 9 9, g32p_row24_traceSegment_049_0666_0009, g32p_row24_traceSegment_049_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 648 36 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 648 18 18, g32p_row24_traceSegment_049_0648_0018, g32p_row24_traceSegment_049_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 684 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 684 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 684 9 9, g32p_row24_traceSegment_049_0684_0009, g32p_row24_traceSegment_049_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 702 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 711 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 702 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 702 9 9, g32p_row24_traceSegment_049_0702_0009, g32p_row24_traceSegment_049_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 684 36 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 684 18 18, g32p_row24_traceSegment_049_0684_0018, g32p_row24_traceSegment_049_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 648 72 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 648 36 36, g32p_row24_traceSegment_049_0648_0036, g32p_row24_traceSegment_049_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 576 144 = [0, 0, 0, 0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 576 72 72, g32p_row24_traceSegment_049_0576_0072, g32p_row24_traceSegment_049_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 720 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 729 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 720 18 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 720 9 9, g32p_row24_traceSegment_049_0720_0009, g32p_row24_traceSegment_049_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 738 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 747 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 738 18 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 738 9 9, g32p_row24_traceSegment_049_0738_0009, g32p_row24_traceSegment_049_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 720 36 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 720 18 18, g32p_row24_traceSegment_049_0720_0018, g32p_row24_traceSegment_049_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 756 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 765 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 756 18 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 756 9 9, g32p_row24_traceSegment_049_0756_0009, g32p_row24_traceSegment_049_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 783 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 774 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 774 9 9, g32p_row24_traceSegment_049_0774_0009, g32p_row24_traceSegment_049_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 756 36 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 756 18 18, g32p_row24_traceSegment_049_0756_0018, g32p_row24_traceSegment_049_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 720 72 = [0, 0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 720 36 36, g32p_row24_traceSegment_049_0720_0036, g32p_row24_traceSegment_049_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 801 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 792 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 792 9 9, g32p_row24_traceSegment_049_0792_0009, g32p_row24_traceSegment_049_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 810 9 9, g32p_row24_traceSegment_049_0810_0009, g32p_row24_traceSegment_049_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 792 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 792 18 18, g32p_row24_traceSegment_049_0792_0018, g32p_row24_traceSegment_049_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 828 9 9, g32p_row24_traceSegment_049_0828_0009, g32p_row24_traceSegment_049_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 846 9 9, g32p_row24_traceSegment_049_0846_0009, g32p_row24_traceSegment_049_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 828 18 18, g32p_row24_traceSegment_049_0828_0018, g32p_row24_traceSegment_049_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 792 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 792 36 36, g32p_row24_traceSegment_049_0792_0036, g32p_row24_traceSegment_049_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 720 144 = [0, 0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 720 72 72, g32p_row24_traceSegment_049_0720_0072, g32p_row24_traceSegment_049_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_049 576 288 = [0, 0, 0, 0, 0, 56] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 576 144 144, g32p_row24_traceSegment_049_0576_0144, g32p_row24_traceSegment_049_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 864 9 9, g32p_row24_traceSegment_049_0864_0009, g32p_row24_traceSegment_049_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 882 9 9, g32p_row24_traceSegment_049_0882_0009, g32p_row24_traceSegment_049_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 864 18 18, g32p_row24_traceSegment_049_0864_0018, g32p_row24_traceSegment_049_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 900 9 9, g32p_row24_traceSegment_049_0900_0009, g32p_row24_traceSegment_049_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 918 9 9, g32p_row24_traceSegment_049_0918_0009, g32p_row24_traceSegment_049_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 900 18 18, g32p_row24_traceSegment_049_0900_0018, g32p_row24_traceSegment_049_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 864 36 36, g32p_row24_traceSegment_049_0864_0036, g32p_row24_traceSegment_049_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 936 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 945 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 936 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 936 9 9, g32p_row24_traceSegment_049_0936_0009, g32p_row24_traceSegment_049_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 954 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 954 18 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 954 9 9, g32p_row24_traceSegment_049_0954_0009, g32p_row24_traceSegment_049_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 936 36 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 936 18 18, g32p_row24_traceSegment_049_0936_0018, g32p_row24_traceSegment_049_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 972 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 981 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 972 18 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 972 9 9, g32p_row24_traceSegment_049_0972_0009, g32p_row24_traceSegment_049_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 990 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 999 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 990 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 990 9 9, g32p_row24_traceSegment_049_0990_0009, g32p_row24_traceSegment_049_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 972 36 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 972 18 18, g32p_row24_traceSegment_049_0972_0018, g32p_row24_traceSegment_049_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 936 72 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 936 36 36, g32p_row24_traceSegment_049_0936_0036, g32p_row24_traceSegment_049_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 864 144 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 864 72 72, g32p_row24_traceSegment_049_0864_0072, g32p_row24_traceSegment_049_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1008 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1017 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1008 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1008 9 9, g32p_row24_traceSegment_049_1008_0009, g32p_row24_traceSegment_049_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1026 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1035 9 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1026 18 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1026 9 9, g32p_row24_traceSegment_049_1026_0009, g32p_row24_traceSegment_049_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 1008 36 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1008 18 18, g32p_row24_traceSegment_049_1008_0018, g32p_row24_traceSegment_049_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1044 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1053 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1044 18 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1044 9 9, g32p_row24_traceSegment_049_1044_0009, g32p_row24_traceSegment_049_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1062 9 9, g32p_row24_traceSegment_049_1062_0009, g32p_row24_traceSegment_049_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 1044 36 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1044 18 18, g32p_row24_traceSegment_049_1044_0018, g32p_row24_traceSegment_049_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 1008 72 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1008 36 36, g32p_row24_traceSegment_049_1008_0036, g32p_row24_traceSegment_049_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1080 9 9, g32p_row24_traceSegment_049_1080_0009, g32p_row24_traceSegment_049_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1098 9 9, g32p_row24_traceSegment_049_1098_0009, g32p_row24_traceSegment_049_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1080 18 18, g32p_row24_traceSegment_049_1080_0018, g32p_row24_traceSegment_049_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1116 9 9, g32p_row24_traceSegment_049_1116_0009, g32p_row24_traceSegment_049_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_049 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_049_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_049 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1134 9 9, g32p_row24_traceSegment_049_1134_0009, g32p_row24_traceSegment_049_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_049 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1116 18 18, g32p_row24_traceSegment_049_1116_0018, g32p_row24_traceSegment_049_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_049 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1080 36 36, g32p_row24_traceSegment_049_1080_0036, g32p_row24_traceSegment_049_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_049_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_049 1008 144 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 1008 72 72, g32p_row24_traceSegment_049_1008_0072, g32p_row24_traceSegment_049_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_049 864 288 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 864 144 144, g32p_row24_traceSegment_049_0864_0144, g32p_row24_traceSegment_049_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_049 576 576 = [0, 0, 0, 0, 0, 86] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 576 288 288, g32p_row24_traceSegment_049_0576_0288, g32p_row24_traceSegment_049_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_049_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_049 0 1152 = [0, 0, 0, 0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_049 0 576 576, g32p_row24_traceSegment_049_0000_0576, g32p_row24_traceSegment_049_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 49 = [0, 0, 0, 0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_049_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row24_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 32) (g32p_literalTraceValue 23 32)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row24_traceCoefficients_032]
  decide +kernel

theorem g32p_row24_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 34) (g32p_literalTraceValue 23 34)
      [1, -1, 1] [3456, 10368, 10368] = true := by
  rw [g32p_row24_traceCoefficients_034]
  decide +kernel

theorem g32p_row24_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 35) (g32p_literalTraceValue 23 35)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row24_traceCoefficients_035]
  decide +kernel

theorem g32p_row24_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 37) (g32p_literalTraceValue 23 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row24_traceCoefficients_037]
  decide +kernel

theorem g32p_row24_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 38) (g32p_literalTraceValue 23 38)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_038]
  decide +kernel

theorem g32p_row24_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 40) (g32p_literalTraceValue 23 40)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_040]
  decide +kernel

theorem g32p_row24_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 45) (g32p_literalTraceValue 23 45)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_045]
  decide +kernel

theorem g32p_row24_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 49) (g32p_literalTraceValue 23 49)
      [1, -1, 1] [0, 0, 3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_049]
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

private def g32p_row24_traceSegment_052 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 52 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_052_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 9 9, g32p_row24_traceSegment_052_0000_0009, g32p_row24_traceSegment_052_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 18 9 9, g32p_row24_traceSegment_052_0018_0009, g32p_row24_traceSegment_052_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 18 18, g32p_row24_traceSegment_052_0000_0018, g32p_row24_traceSegment_052_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 36 9 9, g32p_row24_traceSegment_052_0036_0009, g32p_row24_traceSegment_052_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 54 9 9, g32p_row24_traceSegment_052_0054_0009, g32p_row24_traceSegment_052_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 36 18 18, g32p_row24_traceSegment_052_0036_0018, g32p_row24_traceSegment_052_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 36 36, g32p_row24_traceSegment_052_0000_0036, g32p_row24_traceSegment_052_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 72 9 9, g32p_row24_traceSegment_052_0072_0009, g32p_row24_traceSegment_052_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 90 9 9, g32p_row24_traceSegment_052_0090_0009, g32p_row24_traceSegment_052_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 72 18 18, g32p_row24_traceSegment_052_0072_0018, g32p_row24_traceSegment_052_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 108 9 9, g32p_row24_traceSegment_052_0108_0009, g32p_row24_traceSegment_052_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 126 9 9, g32p_row24_traceSegment_052_0126_0009, g32p_row24_traceSegment_052_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 108 18 18, g32p_row24_traceSegment_052_0108_0018, g32p_row24_traceSegment_052_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 72 36 36, g32p_row24_traceSegment_052_0072_0036, g32p_row24_traceSegment_052_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 72 72, g32p_row24_traceSegment_052_0000_0072, g32p_row24_traceSegment_052_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 144 9 9, g32p_row24_traceSegment_052_0144_0009, g32p_row24_traceSegment_052_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 162 9 9, g32p_row24_traceSegment_052_0162_0009, g32p_row24_traceSegment_052_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 144 18 18, g32p_row24_traceSegment_052_0144_0018, g32p_row24_traceSegment_052_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 180 9 9, g32p_row24_traceSegment_052_0180_0009, g32p_row24_traceSegment_052_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 198 9 9, g32p_row24_traceSegment_052_0198_0009, g32p_row24_traceSegment_052_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 180 18 18, g32p_row24_traceSegment_052_0180_0018, g32p_row24_traceSegment_052_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 144 36 36, g32p_row24_traceSegment_052_0144_0036, g32p_row24_traceSegment_052_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 216 9 9, g32p_row24_traceSegment_052_0216_0009, g32p_row24_traceSegment_052_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 234 9 9, g32p_row24_traceSegment_052_0234_0009, g32p_row24_traceSegment_052_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 216 18 18, g32p_row24_traceSegment_052_0216_0018, g32p_row24_traceSegment_052_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 252 9 9, g32p_row24_traceSegment_052_0252_0009, g32p_row24_traceSegment_052_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 270 9 9, g32p_row24_traceSegment_052_0270_0009, g32p_row24_traceSegment_052_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 252 18 18, g32p_row24_traceSegment_052_0252_0018, g32p_row24_traceSegment_052_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 216 36 36, g32p_row24_traceSegment_052_0216_0036, g32p_row24_traceSegment_052_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 144 72 72, g32p_row24_traceSegment_052_0144_0072, g32p_row24_traceSegment_052_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_052 0 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 144 144, g32p_row24_traceSegment_052_0000_0144, g32p_row24_traceSegment_052_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 288 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 288 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 288 9 9, g32p_row24_traceSegment_052_0288_0009, g32p_row24_traceSegment_052_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 306 9 9, g32p_row24_traceSegment_052_0306_0009, g32p_row24_traceSegment_052_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 288 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 288 18 18, g32p_row24_traceSegment_052_0288_0018, g32p_row24_traceSegment_052_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 324 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 324 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 324 9 9, g32p_row24_traceSegment_052_0324_0009, g32p_row24_traceSegment_052_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 342 9 9, g32p_row24_traceSegment_052_0342_0009, g32p_row24_traceSegment_052_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 324 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 324 18 18, g32p_row24_traceSegment_052_0324_0018, g32p_row24_traceSegment_052_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 288 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 288 36 36, g32p_row24_traceSegment_052_0288_0036, g32p_row24_traceSegment_052_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 360 9 9, g32p_row24_traceSegment_052_0360_0009, g32p_row24_traceSegment_052_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 378 9 9, g32p_row24_traceSegment_052_0378_0009, g32p_row24_traceSegment_052_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 360 18 18, g32p_row24_traceSegment_052_0360_0018, g32p_row24_traceSegment_052_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 396 9 9, g32p_row24_traceSegment_052_0396_0009, g32p_row24_traceSegment_052_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 414 9 9, g32p_row24_traceSegment_052_0414_0009, g32p_row24_traceSegment_052_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 396 18 18, g32p_row24_traceSegment_052_0396_0018, g32p_row24_traceSegment_052_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 360 36 36, g32p_row24_traceSegment_052_0360_0036, g32p_row24_traceSegment_052_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 288 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 288 72 72, g32p_row24_traceSegment_052_0288_0072, g32p_row24_traceSegment_052_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 432 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 432 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 432 9 9, g32p_row24_traceSegment_052_0432_0009, g32p_row24_traceSegment_052_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 450 9 9, g32p_row24_traceSegment_052_0450_0009, g32p_row24_traceSegment_052_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 432 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 432 18 18, g32p_row24_traceSegment_052_0432_0018, g32p_row24_traceSegment_052_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 468 9 9, g32p_row24_traceSegment_052_0468_0009, g32p_row24_traceSegment_052_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 486 9 9, g32p_row24_traceSegment_052_0486_0009, g32p_row24_traceSegment_052_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 468 18 18, g32p_row24_traceSegment_052_0468_0018, g32p_row24_traceSegment_052_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 432 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 432 36 36, g32p_row24_traceSegment_052_0432_0036, g32p_row24_traceSegment_052_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 504 9 9, g32p_row24_traceSegment_052_0504_0009, g32p_row24_traceSegment_052_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 522 9 9, g32p_row24_traceSegment_052_0522_0009, g32p_row24_traceSegment_052_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 504 18 18, g32p_row24_traceSegment_052_0504_0018, g32p_row24_traceSegment_052_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 540 9 9, g32p_row24_traceSegment_052_0540_0009, g32p_row24_traceSegment_052_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 558 9 9, g32p_row24_traceSegment_052_0558_0009, g32p_row24_traceSegment_052_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 540 18 18, g32p_row24_traceSegment_052_0540_0018, g32p_row24_traceSegment_052_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 504 36 36, g32p_row24_traceSegment_052_0504_0036, g32p_row24_traceSegment_052_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 432 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 432 72 72, g32p_row24_traceSegment_052_0432_0072, g32p_row24_traceSegment_052_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_052 288 288 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 288 144 144, g32p_row24_traceSegment_052_0288_0144, g32p_row24_traceSegment_052_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_052 0 576 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 288 288, g32p_row24_traceSegment_052_0000_0288, g32p_row24_traceSegment_052_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 576 9 9, g32p_row24_traceSegment_052_0576_0009, g32p_row24_traceSegment_052_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 603 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 594 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 594 9 9, g32p_row24_traceSegment_052_0594_0009, g32p_row24_traceSegment_052_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 576 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 576 18 18, g32p_row24_traceSegment_052_0576_0018, g32p_row24_traceSegment_052_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 612 9 9, g32p_row24_traceSegment_052_0612_0009, g32p_row24_traceSegment_052_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 630 9 9, g32p_row24_traceSegment_052_0630_0009, g32p_row24_traceSegment_052_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 612 18 18, g32p_row24_traceSegment_052_0612_0018, g32p_row24_traceSegment_052_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 576 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 576 36 36, g32p_row24_traceSegment_052_0576_0036, g32p_row24_traceSegment_052_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 648 9 9, g32p_row24_traceSegment_052_0648_0009, g32p_row24_traceSegment_052_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 666 9 9, g32p_row24_traceSegment_052_0666_0009, g32p_row24_traceSegment_052_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 648 18 18, g32p_row24_traceSegment_052_0648_0018, g32p_row24_traceSegment_052_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 684 9 9, g32p_row24_traceSegment_052_0684_0009, g32p_row24_traceSegment_052_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 711 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 702 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 702 9 9, g32p_row24_traceSegment_052_0702_0009, g32p_row24_traceSegment_052_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 684 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 684 18 18, g32p_row24_traceSegment_052_0684_0018, g32p_row24_traceSegment_052_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 648 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 648 36 36, g32p_row24_traceSegment_052_0648_0036, g32p_row24_traceSegment_052_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 576 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 576 72 72, g32p_row24_traceSegment_052_0576_0072, g32p_row24_traceSegment_052_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 720 9 9, g32p_row24_traceSegment_052_0720_0009, g32p_row24_traceSegment_052_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 738 9 9, g32p_row24_traceSegment_052_0738_0009, g32p_row24_traceSegment_052_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 720 18 18, g32p_row24_traceSegment_052_0720_0018, g32p_row24_traceSegment_052_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 756 9 9, g32p_row24_traceSegment_052_0756_0009, g32p_row24_traceSegment_052_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 774 9 9, g32p_row24_traceSegment_052_0774_0009, g32p_row24_traceSegment_052_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 756 18 18, g32p_row24_traceSegment_052_0756_0018, g32p_row24_traceSegment_052_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 720 36 36, g32p_row24_traceSegment_052_0720_0036, g32p_row24_traceSegment_052_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 792 9 9, g32p_row24_traceSegment_052_0792_0009, g32p_row24_traceSegment_052_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 810 9 9, g32p_row24_traceSegment_052_0810_0009, g32p_row24_traceSegment_052_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 792 18 18, g32p_row24_traceSegment_052_0792_0018, g32p_row24_traceSegment_052_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 828 9 9, g32p_row24_traceSegment_052_0828_0009, g32p_row24_traceSegment_052_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 846 9 9, g32p_row24_traceSegment_052_0846_0009, g32p_row24_traceSegment_052_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 828 18 18, g32p_row24_traceSegment_052_0828_0018, g32p_row24_traceSegment_052_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 792 36 36, g32p_row24_traceSegment_052_0792_0036, g32p_row24_traceSegment_052_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 720 72 72, g32p_row24_traceSegment_052_0720_0072, g32p_row24_traceSegment_052_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_052 576 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 576 144 144, g32p_row24_traceSegment_052_0576_0144, g32p_row24_traceSegment_052_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 864 9 9, g32p_row24_traceSegment_052_0864_0009, g32p_row24_traceSegment_052_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 882 9 9, g32p_row24_traceSegment_052_0882_0009, g32p_row24_traceSegment_052_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 864 18 18, g32p_row24_traceSegment_052_0864_0018, g32p_row24_traceSegment_052_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 900 9 9, g32p_row24_traceSegment_052_0900_0009, g32p_row24_traceSegment_052_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 918 9 9, g32p_row24_traceSegment_052_0918_0009, g32p_row24_traceSegment_052_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 900 18 18, g32p_row24_traceSegment_052_0900_0018, g32p_row24_traceSegment_052_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 864 36 36, g32p_row24_traceSegment_052_0864_0036, g32p_row24_traceSegment_052_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 936 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 945 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 936 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 936 9 9, g32p_row24_traceSegment_052_0936_0009, g32p_row24_traceSegment_052_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 954 9 9, g32p_row24_traceSegment_052_0954_0009, g32p_row24_traceSegment_052_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 936 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 936 18 18, g32p_row24_traceSegment_052_0936_0018, g32p_row24_traceSegment_052_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 972 9 9, g32p_row24_traceSegment_052_0972_0009, g32p_row24_traceSegment_052_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 990 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 990 9 9, g32p_row24_traceSegment_052_0990_0009, g32p_row24_traceSegment_052_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 972 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 972 18 18, g32p_row24_traceSegment_052_0972_0018, g32p_row24_traceSegment_052_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 936 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 936 36 36, g32p_row24_traceSegment_052_0936_0036, g32p_row24_traceSegment_052_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 864 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 864 72 72, g32p_row24_traceSegment_052_0864_0072, g32p_row24_traceSegment_052_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1008 9 9, g32p_row24_traceSegment_052_1008_0009, g32p_row24_traceSegment_052_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1026 9 9, g32p_row24_traceSegment_052_1026_0009, g32p_row24_traceSegment_052_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1008 18 18, g32p_row24_traceSegment_052_1008_0018, g32p_row24_traceSegment_052_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1044 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1044 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1044 9 9, g32p_row24_traceSegment_052_1044_0009, g32p_row24_traceSegment_052_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1062 9 9, g32p_row24_traceSegment_052_1062_0009, g32p_row24_traceSegment_052_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 1044 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1044 18 18, g32p_row24_traceSegment_052_1044_0018, g32p_row24_traceSegment_052_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 1008 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1008 36 36, g32p_row24_traceSegment_052_1008_0036, g32p_row24_traceSegment_052_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1080 9 9, g32p_row24_traceSegment_052_1080_0009, g32p_row24_traceSegment_052_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1098 9 9, g32p_row24_traceSegment_052_1098_0009, g32p_row24_traceSegment_052_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1080 18 18, g32p_row24_traceSegment_052_1080_0018, g32p_row24_traceSegment_052_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1116 9 9, g32p_row24_traceSegment_052_1116_0009, g32p_row24_traceSegment_052_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_052 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_052_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_052 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1134 9 9, g32p_row24_traceSegment_052_1134_0009, g32p_row24_traceSegment_052_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_052 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1116 18 18, g32p_row24_traceSegment_052_1116_0018, g32p_row24_traceSegment_052_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_052 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1080 36 36, g32p_row24_traceSegment_052_1080_0036, g32p_row24_traceSegment_052_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_052_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_052 1008 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 1008 72 72, g32p_row24_traceSegment_052_1008_0072, g32p_row24_traceSegment_052_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_052 864 288 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 864 144 144, g32p_row24_traceSegment_052_0864_0144, g32p_row24_traceSegment_052_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_052 576 576 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 576 288 288, g32p_row24_traceSegment_052_0576_0288, g32p_row24_traceSegment_052_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_052_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_052 0 1152 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_052 0 576 576, g32p_row24_traceSegment_052_0000_0576, g32p_row24_traceSegment_052_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 52 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_052_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_057_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 0 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 9 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 0 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 9 9, g32p_row24_traceSegment_057_0000_0009, g32p_row24_traceSegment_057_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 27 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 18 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 18 9 9, g32p_row24_traceSegment_057_0018_0009, g32p_row24_traceSegment_057_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 0 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 18 18, g32p_row24_traceSegment_057_0000_0018, g32p_row24_traceSegment_057_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 36 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 45 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 36 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 36 9 9, g32p_row24_traceSegment_057_0036_0009, g32p_row24_traceSegment_057_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 54 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 54 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 54 9 9, g32p_row24_traceSegment_057_0054_0009, g32p_row24_traceSegment_057_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 36 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 36 18 18, g32p_row24_traceSegment_057_0036_0018, g32p_row24_traceSegment_057_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 0 72 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 36 36, g32p_row24_traceSegment_057_0000_0036, g32p_row24_traceSegment_057_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 81 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 72 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 72 9 9, g32p_row24_traceSegment_057_0072_0009, g32p_row24_traceSegment_057_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 90 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 99 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 90 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 90 9 9, g32p_row24_traceSegment_057_0090_0009, g32p_row24_traceSegment_057_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 72 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 72 18 18, g32p_row24_traceSegment_057_0072_0018, g32p_row24_traceSegment_057_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 108 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 117 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 108 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 108 9 9, g32p_row24_traceSegment_057_0108_0009, g32p_row24_traceSegment_057_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 126 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 135 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 126 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 126 9 9, g32p_row24_traceSegment_057_0126_0009, g32p_row24_traceSegment_057_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 108 36 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 108 18 18, g32p_row24_traceSegment_057_0108_0018, g32p_row24_traceSegment_057_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 72 72 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 72 36 36, g32p_row24_traceSegment_057_0072_0036, g32p_row24_traceSegment_057_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 0 144 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 72 72, g32p_row24_traceSegment_057_0000_0072, g32p_row24_traceSegment_057_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 144 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 153 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 144 18 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 144 9 9, g32p_row24_traceSegment_057_0144_0009, g32p_row24_traceSegment_057_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 162 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 171 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 162 18 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 162 9 9, g32p_row24_traceSegment_057_0162_0009, g32p_row24_traceSegment_057_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 144 36 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 144 18 18, g32p_row24_traceSegment_057_0144_0018, g32p_row24_traceSegment_057_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 180 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 189 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 180 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 180 9 9, g32p_row24_traceSegment_057_0180_0009, g32p_row24_traceSegment_057_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 198 9 9, g32p_row24_traceSegment_057_0198_0009, g32p_row24_traceSegment_057_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 180 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 180 18 18, g32p_row24_traceSegment_057_0180_0018, g32p_row24_traceSegment_057_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 144 72 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 144 36 36, g32p_row24_traceSegment_057_0144_0036, g32p_row24_traceSegment_057_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 216 9 9, g32p_row24_traceSegment_057_0216_0009, g32p_row24_traceSegment_057_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 243 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 234 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 234 9 9, g32p_row24_traceSegment_057_0234_0009, g32p_row24_traceSegment_057_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 216 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 216 18 18, g32p_row24_traceSegment_057_0216_0018, g32p_row24_traceSegment_057_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 252 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 252 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 252 9 9, g32p_row24_traceSegment_057_0252_0009, g32p_row24_traceSegment_057_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 270 9 9, g32p_row24_traceSegment_057_0270_0009, g32p_row24_traceSegment_057_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 252 18 18, g32p_row24_traceSegment_057_0252_0018, g32p_row24_traceSegment_057_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 216 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 216 36 36, g32p_row24_traceSegment_057_0216_0036, g32p_row24_traceSegment_057_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 144 144 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 144 72 72, g32p_row24_traceSegment_057_0144_0072, g32p_row24_traceSegment_057_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_057 0 288 = [0, 45] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 144 144, g32p_row24_traceSegment_057_0000_0144, g32p_row24_traceSegment_057_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 288 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 297 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 288 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 288 9 9, g32p_row24_traceSegment_057_0288_0009, g32p_row24_traceSegment_057_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 306 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 315 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 306 18 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 306 9 9, g32p_row24_traceSegment_057_0306_0009, g32p_row24_traceSegment_057_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 288 36 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 288 18 18, g32p_row24_traceSegment_057_0288_0018, g32p_row24_traceSegment_057_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 324 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 333 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 324 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 324 9 9, g32p_row24_traceSegment_057_0324_0009, g32p_row24_traceSegment_057_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 342 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 351 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 342 18 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 342 9 9, g32p_row24_traceSegment_057_0342_0009, g32p_row24_traceSegment_057_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 324 36 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 324 18 18, g32p_row24_traceSegment_057_0324_0018, g32p_row24_traceSegment_057_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 288 72 = [0, 21] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 288 36 36, g32p_row24_traceSegment_057_0288_0036, g32p_row24_traceSegment_057_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 360 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 369 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 360 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 360 9 9, g32p_row24_traceSegment_057_0360_0009, g32p_row24_traceSegment_057_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 378 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 387 9 = [0, 5] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 378 18 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 378 9 9, g32p_row24_traceSegment_057_0378_0009, g32p_row24_traceSegment_057_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 360 36 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 360 18 18, g32p_row24_traceSegment_057_0360_0018, g32p_row24_traceSegment_057_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 405 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 396 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 396 9 9, g32p_row24_traceSegment_057_0396_0009, g32p_row24_traceSegment_057_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 414 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 423 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 414 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 414 9 9, g32p_row24_traceSegment_057_0414_0009, g32p_row24_traceSegment_057_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 396 36 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 396 18 18, g32p_row24_traceSegment_057_0396_0018, g32p_row24_traceSegment_057_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 360 72 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 360 36 36, g32p_row24_traceSegment_057_0360_0036, g32p_row24_traceSegment_057_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 288 144 = [0, 41] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 288 72 72, g32p_row24_traceSegment_057_0288_0072, g32p_row24_traceSegment_057_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 432 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 441 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 432 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 432 9 9, g32p_row24_traceSegment_057_0432_0009, g32p_row24_traceSegment_057_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 459 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 450 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 450 9 9, g32p_row24_traceSegment_057_0450_0009, g32p_row24_traceSegment_057_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 432 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 432 18 18, g32p_row24_traceSegment_057_0432_0018, g32p_row24_traceSegment_057_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 468 9 9, g32p_row24_traceSegment_057_0468_0009, g32p_row24_traceSegment_057_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 486 9 9, g32p_row24_traceSegment_057_0486_0009, g32p_row24_traceSegment_057_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 468 18 18, g32p_row24_traceSegment_057_0468_0018, g32p_row24_traceSegment_057_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 432 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 432 36 36, g32p_row24_traceSegment_057_0432_0036, g32p_row24_traceSegment_057_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 513 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 504 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 504 9 9, g32p_row24_traceSegment_057_0504_0009, g32p_row24_traceSegment_057_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 522 9 9, g32p_row24_traceSegment_057_0522_0009, g32p_row24_traceSegment_057_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 504 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 504 18 18, g32p_row24_traceSegment_057_0504_0018, g32p_row24_traceSegment_057_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 540 9 9, g32p_row24_traceSegment_057_0540_0009, g32p_row24_traceSegment_057_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 558 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 558 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 558 9 9, g32p_row24_traceSegment_057_0558_0009, g32p_row24_traceSegment_057_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 540 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 540 18 18, g32p_row24_traceSegment_057_0540_0018, g32p_row24_traceSegment_057_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 504 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 504 36 36, g32p_row24_traceSegment_057_0504_0036, g32p_row24_traceSegment_057_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 432 144 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 432 72 72, g32p_row24_traceSegment_057_0432_0072, g32p_row24_traceSegment_057_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_057 288 288 = [0, 49] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 288 144 144, g32p_row24_traceSegment_057_0288_0144, g32p_row24_traceSegment_057_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_057 0 576 = [0, 94] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 288 288, g32p_row24_traceSegment_057_0000_0288, g32p_row24_traceSegment_057_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 576 9 9, g32p_row24_traceSegment_057_0576_0009, g32p_row24_traceSegment_057_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 594 9 9, g32p_row24_traceSegment_057_0594_0009, g32p_row24_traceSegment_057_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 576 18 18, g32p_row24_traceSegment_057_0576_0018, g32p_row24_traceSegment_057_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 612 9 9, g32p_row24_traceSegment_057_0612_0009, g32p_row24_traceSegment_057_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 639 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 630 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 630 9 9, g32p_row24_traceSegment_057_0630_0009, g32p_row24_traceSegment_057_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 612 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 612 18 18, g32p_row24_traceSegment_057_0612_0018, g32p_row24_traceSegment_057_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 576 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 576 36 36, g32p_row24_traceSegment_057_0576_0036, g32p_row24_traceSegment_057_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 648 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 657 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 648 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 648 9 9, g32p_row24_traceSegment_057_0648_0009, g32p_row24_traceSegment_057_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 666 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 675 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 666 18 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 666 9 9, g32p_row24_traceSegment_057_0666_0009, g32p_row24_traceSegment_057_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 648 36 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 648 18 18, g32p_row24_traceSegment_057_0648_0018, g32p_row24_traceSegment_057_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 684 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 693 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 684 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 684 9 9, g32p_row24_traceSegment_057_0684_0009, g32p_row24_traceSegment_057_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 702 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 702 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 702 9 9, g32p_row24_traceSegment_057_0702_0009, g32p_row24_traceSegment_057_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 684 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 684 18 18, g32p_row24_traceSegment_057_0684_0018, g32p_row24_traceSegment_057_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 648 72 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 648 36 36, g32p_row24_traceSegment_057_0648_0036, g32p_row24_traceSegment_057_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 576 144 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 576 72 72, g32p_row24_traceSegment_057_0576_0072, g32p_row24_traceSegment_057_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 720 9 9, g32p_row24_traceSegment_057_0720_0009, g32p_row24_traceSegment_057_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 738 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 747 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 738 18 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 738 9 9, g32p_row24_traceSegment_057_0738_0009, g32p_row24_traceSegment_057_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 720 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 720 18 18, g32p_row24_traceSegment_057_0720_0018, g32p_row24_traceSegment_057_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 756 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 756 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 756 9 9, g32p_row24_traceSegment_057_0756_0009, g32p_row24_traceSegment_057_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 774 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 783 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 774 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 774 9 9, g32p_row24_traceSegment_057_0774_0009, g32p_row24_traceSegment_057_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 756 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 756 18 18, g32p_row24_traceSegment_057_0756_0018, g32p_row24_traceSegment_057_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 720 72 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 720 36 36, g32p_row24_traceSegment_057_0720_0036, g32p_row24_traceSegment_057_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 792 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 801 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 792 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 792 9 9, g32p_row24_traceSegment_057_0792_0009, g32p_row24_traceSegment_057_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 810 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 819 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 810 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 810 9 9, g32p_row24_traceSegment_057_0810_0009, g32p_row24_traceSegment_057_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 792 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 792 18 18, g32p_row24_traceSegment_057_0792_0018, g32p_row24_traceSegment_057_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 828 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 837 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 828 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 828 9 9, g32p_row24_traceSegment_057_0828_0009, g32p_row24_traceSegment_057_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 846 9 9, g32p_row24_traceSegment_057_0846_0009, g32p_row24_traceSegment_057_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 828 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 828 18 18, g32p_row24_traceSegment_057_0828_0018, g32p_row24_traceSegment_057_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 792 72 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 792 36 36, g32p_row24_traceSegment_057_0792_0036, g32p_row24_traceSegment_057_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 720 144 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 720 72 72, g32p_row24_traceSegment_057_0720_0072, g32p_row24_traceSegment_057_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_057 576 288 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 576 144 144, g32p_row24_traceSegment_057_0576_0144, g32p_row24_traceSegment_057_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 873 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 864 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 864 9 9, g32p_row24_traceSegment_057_0864_0009, g32p_row24_traceSegment_057_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 882 9 9, g32p_row24_traceSegment_057_0882_0009, g32p_row24_traceSegment_057_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 864 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 864 18 18, g32p_row24_traceSegment_057_0864_0018, g32p_row24_traceSegment_057_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 909 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 900 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 900 9 9, g32p_row24_traceSegment_057_0900_0009, g32p_row24_traceSegment_057_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 918 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 918 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 918 9 9, g32p_row24_traceSegment_057_0918_0009, g32p_row24_traceSegment_057_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 900 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 900 18 18, g32p_row24_traceSegment_057_0900_0018, g32p_row24_traceSegment_057_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 864 72 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 864 36 36, g32p_row24_traceSegment_057_0864_0036, g32p_row24_traceSegment_057_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 936 9 9, g32p_row24_traceSegment_057_0936_0009, g32p_row24_traceSegment_057_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 954 9 9, g32p_row24_traceSegment_057_0954_0009, g32p_row24_traceSegment_057_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 936 18 18, g32p_row24_traceSegment_057_0936_0018, g32p_row24_traceSegment_057_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 972 9 9, g32p_row24_traceSegment_057_0972_0009, g32p_row24_traceSegment_057_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 999 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 990 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 990 9 9, g32p_row24_traceSegment_057_0990_0009, g32p_row24_traceSegment_057_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 972 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 972 18 18, g32p_row24_traceSegment_057_0972_0018, g32p_row24_traceSegment_057_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 936 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 936 36 36, g32p_row24_traceSegment_057_0936_0036, g32p_row24_traceSegment_057_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 864 144 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 864 72 72, g32p_row24_traceSegment_057_0864_0072, g32p_row24_traceSegment_057_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1008 9 9, g32p_row24_traceSegment_057_1008_0009, g32p_row24_traceSegment_057_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1035 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1026 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1026 9 9, g32p_row24_traceSegment_057_1026_0009, g32p_row24_traceSegment_057_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 1008 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1008 18 18, g32p_row24_traceSegment_057_1008_0018, g32p_row24_traceSegment_057_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1044 9 9, g32p_row24_traceSegment_057_1044_0009, g32p_row24_traceSegment_057_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1062 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1071 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1062 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1062 9 9, g32p_row24_traceSegment_057_1062_0009, g32p_row24_traceSegment_057_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 1044 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1044 18 18, g32p_row24_traceSegment_057_1044_0018, g32p_row24_traceSegment_057_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 1008 72 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1008 36 36, g32p_row24_traceSegment_057_1008_0036, g32p_row24_traceSegment_057_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1080 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1089 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1080 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1080 9 9, g32p_row24_traceSegment_057_1080_0009, g32p_row24_traceSegment_057_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1098 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1098 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1098 9 9, g32p_row24_traceSegment_057_1098_0009, g32p_row24_traceSegment_057_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 1080 36 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1080 18 18, g32p_row24_traceSegment_057_1080_0018, g32p_row24_traceSegment_057_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1116 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1116 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1116 9 9, g32p_row24_traceSegment_057_1116_0009, g32p_row24_traceSegment_057_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_057 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_057_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_057 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1134 9 9, g32p_row24_traceSegment_057_1134_0009, g32p_row24_traceSegment_057_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_057 1116 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1116 18 18, g32p_row24_traceSegment_057_1116_0018, g32p_row24_traceSegment_057_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_057 1080 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1080 36 36, g32p_row24_traceSegment_057_1080_0036, g32p_row24_traceSegment_057_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_057_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_057 1008 144 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 1008 72 72, g32p_row24_traceSegment_057_1008_0072, g32p_row24_traceSegment_057_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_057 864 288 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 864 144 144, g32p_row24_traceSegment_057_0864_0144, g32p_row24_traceSegment_057_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_057 576 576 = [0, 50] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 576 288 288, g32p_row24_traceSegment_057_0576_0288, g32p_row24_traceSegment_057_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_057_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_057 0 1152 = [0, 144] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_057 0 576 576, g32p_row24_traceSegment_057_0000_0576, g32p_row24_traceSegment_057_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 57 = [0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_057_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_065_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 9 9, g32p_row24_traceSegment_065_0000_0009, g32p_row24_traceSegment_065_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 27 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 18 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 18 9 9, g32p_row24_traceSegment_065_0018_0009, g32p_row24_traceSegment_065_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 0 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 18 18, g32p_row24_traceSegment_065_0000_0018, g32p_row24_traceSegment_065_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 45 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 36 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 36 9 9, g32p_row24_traceSegment_065_0036_0009, g32p_row24_traceSegment_065_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 63 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 54 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 54 9 9, g32p_row24_traceSegment_065_0054_0009, g32p_row24_traceSegment_065_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 36 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 36 18 18, g32p_row24_traceSegment_065_0036_0018, g32p_row24_traceSegment_065_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 0 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 36 36, g32p_row24_traceSegment_065_0000_0036, g32p_row24_traceSegment_065_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 72 9 9, g32p_row24_traceSegment_065_0072_0009, g32p_row24_traceSegment_065_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 90 9 9, g32p_row24_traceSegment_065_0090_0009, g32p_row24_traceSegment_065_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 72 18 18, g32p_row24_traceSegment_065_0072_0018, g32p_row24_traceSegment_065_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 108 9 9, g32p_row24_traceSegment_065_0108_0009, g32p_row24_traceSegment_065_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 126 9 9, g32p_row24_traceSegment_065_0126_0009, g32p_row24_traceSegment_065_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 108 18 18, g32p_row24_traceSegment_065_0108_0018, g32p_row24_traceSegment_065_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 72 36 36, g32p_row24_traceSegment_065_0072_0036, g32p_row24_traceSegment_065_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 0 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 72 72, g32p_row24_traceSegment_065_0000_0072, g32p_row24_traceSegment_065_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 144 9 9, g32p_row24_traceSegment_065_0144_0009, g32p_row24_traceSegment_065_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 162 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 171 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 162 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 162 9 9, g32p_row24_traceSegment_065_0162_0009, g32p_row24_traceSegment_065_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 144 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 144 18 18, g32p_row24_traceSegment_065_0144_0018, g32p_row24_traceSegment_065_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 189 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 180 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 180 9 9, g32p_row24_traceSegment_065_0180_0009, g32p_row24_traceSegment_065_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 198 9 9, g32p_row24_traceSegment_065_0198_0009, g32p_row24_traceSegment_065_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 180 18 18, g32p_row24_traceSegment_065_0180_0018, g32p_row24_traceSegment_065_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 144 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 144 36 36, g32p_row24_traceSegment_065_0144_0036, g32p_row24_traceSegment_065_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 216 9 9, g32p_row24_traceSegment_065_0216_0009, g32p_row24_traceSegment_065_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 234 9 9, g32p_row24_traceSegment_065_0234_0009, g32p_row24_traceSegment_065_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 216 18 18, g32p_row24_traceSegment_065_0216_0018, g32p_row24_traceSegment_065_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 252 9 9, g32p_row24_traceSegment_065_0252_0009, g32p_row24_traceSegment_065_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 270 9 9, g32p_row24_traceSegment_065_0270_0009, g32p_row24_traceSegment_065_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 252 18 18, g32p_row24_traceSegment_065_0252_0018, g32p_row24_traceSegment_065_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 216 36 36, g32p_row24_traceSegment_065_0216_0036, g32p_row24_traceSegment_065_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 144 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 144 72 72, g32p_row24_traceSegment_065_0144_0072, g32p_row24_traceSegment_065_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_065 0 288 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 144 144, g32p_row24_traceSegment_065_0000_0144, g32p_row24_traceSegment_065_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 288 9 9, g32p_row24_traceSegment_065_0288_0009, g32p_row24_traceSegment_065_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 306 9 9, g32p_row24_traceSegment_065_0306_0009, g32p_row24_traceSegment_065_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 288 18 18, g32p_row24_traceSegment_065_0288_0018, g32p_row24_traceSegment_065_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 324 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 324 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 324 9 9, g32p_row24_traceSegment_065_0324_0009, g32p_row24_traceSegment_065_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 342 9 9, g32p_row24_traceSegment_065_0342_0009, g32p_row24_traceSegment_065_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 324 18 18, g32p_row24_traceSegment_065_0324_0018, g32p_row24_traceSegment_065_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 288 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 288 36 36, g32p_row24_traceSegment_065_0288_0036, g32p_row24_traceSegment_065_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 360 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 360 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 360 9 9, g32p_row24_traceSegment_065_0360_0009, g32p_row24_traceSegment_065_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 378 9 9, g32p_row24_traceSegment_065_0378_0009, g32p_row24_traceSegment_065_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 360 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 360 18 18, g32p_row24_traceSegment_065_0360_0018, g32p_row24_traceSegment_065_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 396 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 396 9 9, g32p_row24_traceSegment_065_0396_0009, g32p_row24_traceSegment_065_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 414 9 9, g32p_row24_traceSegment_065_0414_0009, g32p_row24_traceSegment_065_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 396 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 396 18 18, g32p_row24_traceSegment_065_0396_0018, g32p_row24_traceSegment_065_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 360 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 360 36 36, g32p_row24_traceSegment_065_0360_0036, g32p_row24_traceSegment_065_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 288 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 288 72 72, g32p_row24_traceSegment_065_0288_0072, g32p_row24_traceSegment_065_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 441 9 = [0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 432 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 432 9 9, g32p_row24_traceSegment_065_0432_0009, g32p_row24_traceSegment_065_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 450 9 9, g32p_row24_traceSegment_065_0450_0009, g32p_row24_traceSegment_065_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 432 36 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 432 18 18, g32p_row24_traceSegment_065_0432_0018, g32p_row24_traceSegment_065_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 468 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 468 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 468 9 9, g32p_row24_traceSegment_065_0468_0009, g32p_row24_traceSegment_065_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 486 9 9, g32p_row24_traceSegment_065_0486_0009, g32p_row24_traceSegment_065_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 468 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 468 18 18, g32p_row24_traceSegment_065_0468_0018, g32p_row24_traceSegment_065_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 432 72 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 432 36 36, g32p_row24_traceSegment_065_0432_0036, g32p_row24_traceSegment_065_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 504 9 9, g32p_row24_traceSegment_065_0504_0009, g32p_row24_traceSegment_065_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 522 9 9, g32p_row24_traceSegment_065_0522_0009, g32p_row24_traceSegment_065_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 504 18 18, g32p_row24_traceSegment_065_0504_0018, g32p_row24_traceSegment_065_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 540 9 9, g32p_row24_traceSegment_065_0540_0009, g32p_row24_traceSegment_065_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 558 9 9, g32p_row24_traceSegment_065_0558_0009, g32p_row24_traceSegment_065_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 540 18 18, g32p_row24_traceSegment_065_0540_0018, g32p_row24_traceSegment_065_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 504 36 36, g32p_row24_traceSegment_065_0504_0036, g32p_row24_traceSegment_065_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 432 144 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 432 72 72, g32p_row24_traceSegment_065_0432_0072, g32p_row24_traceSegment_065_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_065 288 288 = [0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 288 144 144, g32p_row24_traceSegment_065_0288_0144, g32p_row24_traceSegment_065_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_065 0 576 = [0, 12, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 288 288, g32p_row24_traceSegment_065_0000_0288, g32p_row24_traceSegment_065_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 576 9 9, g32p_row24_traceSegment_065_0576_0009, g32p_row24_traceSegment_065_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 594 9 9, g32p_row24_traceSegment_065_0594_0009, g32p_row24_traceSegment_065_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 576 18 18, g32p_row24_traceSegment_065_0576_0018, g32p_row24_traceSegment_065_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 612 9 9, g32p_row24_traceSegment_065_0612_0009, g32p_row24_traceSegment_065_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 630 9 9, g32p_row24_traceSegment_065_0630_0009, g32p_row24_traceSegment_065_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 612 18 18, g32p_row24_traceSegment_065_0612_0018, g32p_row24_traceSegment_065_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 576 36 36, g32p_row24_traceSegment_065_0576_0036, g32p_row24_traceSegment_065_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 648 9 9, g32p_row24_traceSegment_065_0648_0009, g32p_row24_traceSegment_065_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 666 9 9, g32p_row24_traceSegment_065_0666_0009, g32p_row24_traceSegment_065_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 648 18 18, g32p_row24_traceSegment_065_0648_0018, g32p_row24_traceSegment_065_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 684 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 684 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 684 9 9, g32p_row24_traceSegment_065_0684_0009, g32p_row24_traceSegment_065_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 702 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 702 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 702 9 9, g32p_row24_traceSegment_065_0702_0009, g32p_row24_traceSegment_065_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 684 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 684 18 18, g32p_row24_traceSegment_065_0684_0018, g32p_row24_traceSegment_065_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 648 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 648 36 36, g32p_row24_traceSegment_065_0648_0036, g32p_row24_traceSegment_065_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 576 144 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 576 72 72, g32p_row24_traceSegment_065_0576_0072, g32p_row24_traceSegment_065_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 720 9 9, g32p_row24_traceSegment_065_0720_0009, g32p_row24_traceSegment_065_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 738 9 9, g32p_row24_traceSegment_065_0738_0009, g32p_row24_traceSegment_065_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 720 18 18, g32p_row24_traceSegment_065_0720_0018, g32p_row24_traceSegment_065_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 765 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 756 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 756 9 9, g32p_row24_traceSegment_065_0756_0009, g32p_row24_traceSegment_065_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 774 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 783 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 774 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 774 9 9, g32p_row24_traceSegment_065_0774_0009, g32p_row24_traceSegment_065_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 756 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 756 18 18, g32p_row24_traceSegment_065_0756_0018, g32p_row24_traceSegment_065_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 720 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 720 36 36, g32p_row24_traceSegment_065_0720_0036, g32p_row24_traceSegment_065_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 792 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 801 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 792 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 792 9 9, g32p_row24_traceSegment_065_0792_0009, g32p_row24_traceSegment_065_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 810 9 9, g32p_row24_traceSegment_065_0810_0009, g32p_row24_traceSegment_065_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 792 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 792 18 18, g32p_row24_traceSegment_065_0792_0018, g32p_row24_traceSegment_065_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 828 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 828 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 828 9 9, g32p_row24_traceSegment_065_0828_0009, g32p_row24_traceSegment_065_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 846 9 9, g32p_row24_traceSegment_065_0846_0009, g32p_row24_traceSegment_065_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 828 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 828 18 18, g32p_row24_traceSegment_065_0828_0018, g32p_row24_traceSegment_065_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 792 72 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 792 36 36, g32p_row24_traceSegment_065_0792_0036, g32p_row24_traceSegment_065_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 720 144 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 720 72 72, g32p_row24_traceSegment_065_0720_0072, g32p_row24_traceSegment_065_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_065 576 288 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 576 144 144, g32p_row24_traceSegment_065_0576_0144, g32p_row24_traceSegment_065_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 864 9 9, g32p_row24_traceSegment_065_0864_0009, g32p_row24_traceSegment_065_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 882 9 9, g32p_row24_traceSegment_065_0882_0009, g32p_row24_traceSegment_065_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 864 18 18, g32p_row24_traceSegment_065_0864_0018, g32p_row24_traceSegment_065_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 900 9 9, g32p_row24_traceSegment_065_0900_0009, g32p_row24_traceSegment_065_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 927 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 918 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 918 9 9, g32p_row24_traceSegment_065_0918_0009, g32p_row24_traceSegment_065_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 900 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 900 18 18, g32p_row24_traceSegment_065_0900_0018, g32p_row24_traceSegment_065_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 864 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 864 36 36, g32p_row24_traceSegment_065_0864_0036, g32p_row24_traceSegment_065_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 936 9 9, g32p_row24_traceSegment_065_0936_0009, g32p_row24_traceSegment_065_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 954 9 9, g32p_row24_traceSegment_065_0954_0009, g32p_row24_traceSegment_065_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 936 18 18, g32p_row24_traceSegment_065_0936_0018, g32p_row24_traceSegment_065_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 972 9 9, g32p_row24_traceSegment_065_0972_0009, g32p_row24_traceSegment_065_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 990 9 9, g32p_row24_traceSegment_065_0990_0009, g32p_row24_traceSegment_065_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 972 18 18, g32p_row24_traceSegment_065_0972_0018, g32p_row24_traceSegment_065_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 936 36 36, g32p_row24_traceSegment_065_0936_0036, g32p_row24_traceSegment_065_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 864 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 864 72 72, g32p_row24_traceSegment_065_0864_0072, g32p_row24_traceSegment_065_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1008 9 9, g32p_row24_traceSegment_065_1008_0009, g32p_row24_traceSegment_065_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1026 9 9, g32p_row24_traceSegment_065_1026_0009, g32p_row24_traceSegment_065_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1008 18 18, g32p_row24_traceSegment_065_1008_0018, g32p_row24_traceSegment_065_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1044 9 9, g32p_row24_traceSegment_065_1044_0009, g32p_row24_traceSegment_065_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1071 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1062 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1062 9 9, g32p_row24_traceSegment_065_1062_0009, g32p_row24_traceSegment_065_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 1044 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1044 18 18, g32p_row24_traceSegment_065_1044_0018, g32p_row24_traceSegment_065_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 1008 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1008 36 36, g32p_row24_traceSegment_065_1008_0036, g32p_row24_traceSegment_065_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1080 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1080 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1080 9 9, g32p_row24_traceSegment_065_1080_0009, g32p_row24_traceSegment_065_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1098 9 9, g32p_row24_traceSegment_065_1098_0009, g32p_row24_traceSegment_065_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 1080 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1080 18 18, g32p_row24_traceSegment_065_1080_0018, g32p_row24_traceSegment_065_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1116 9 9, g32p_row24_traceSegment_065_1116_0009, g32p_row24_traceSegment_065_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_065 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_065_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_065 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1134 9 9, g32p_row24_traceSegment_065_1134_0009, g32p_row24_traceSegment_065_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_065 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1116 18 18, g32p_row24_traceSegment_065_1116_0018, g32p_row24_traceSegment_065_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_065 1080 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1080 36 36, g32p_row24_traceSegment_065_1080_0036, g32p_row24_traceSegment_065_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_065_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_065 1008 144 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 1008 72 72, g32p_row24_traceSegment_065_1008_0072, g32p_row24_traceSegment_065_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_065 864 288 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 864 144 144, g32p_row24_traceSegment_065_0864_0144, g32p_row24_traceSegment_065_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_065 576 576 = [0, 12, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 576 288 288, g32p_row24_traceSegment_065_0576_0288, g32p_row24_traceSegment_065_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_065_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_065 0 1152 = [0, 24, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_065 0 576 576, g32p_row24_traceSegment_065_0000_0576, g32p_row24_traceSegment_065_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 65 = [0, 24, 0, 0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_065_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_066 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 66 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_066_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 9 9, g32p_row24_traceSegment_066_0000_0009, g32p_row24_traceSegment_066_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 18 9 9, g32p_row24_traceSegment_066_0018_0009, g32p_row24_traceSegment_066_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 18 18, g32p_row24_traceSegment_066_0000_0018, g32p_row24_traceSegment_066_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 36 9 9, g32p_row24_traceSegment_066_0036_0009, g32p_row24_traceSegment_066_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 54 9 9, g32p_row24_traceSegment_066_0054_0009, g32p_row24_traceSegment_066_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 36 18 18, g32p_row24_traceSegment_066_0036_0018, g32p_row24_traceSegment_066_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 36 36, g32p_row24_traceSegment_066_0000_0036, g32p_row24_traceSegment_066_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 81 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 72 9 9, g32p_row24_traceSegment_066_0072_0009, g32p_row24_traceSegment_066_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 99 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 90 9 9, g32p_row24_traceSegment_066_0090_0009, g32p_row24_traceSegment_066_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 72 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 72 18 18, g32p_row24_traceSegment_066_0072_0018, g32p_row24_traceSegment_066_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 108 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 117 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 108 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 108 9 9, g32p_row24_traceSegment_066_0108_0009, g32p_row24_traceSegment_066_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 126 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 126 9 9, g32p_row24_traceSegment_066_0126_0009, g32p_row24_traceSegment_066_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 108 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 108 18 18, g32p_row24_traceSegment_066_0108_0018, g32p_row24_traceSegment_066_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 72 72 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 72 36 36, g32p_row24_traceSegment_066_0072_0036, g32p_row24_traceSegment_066_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 0 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 72 72, g32p_row24_traceSegment_066_0000_0072, g32p_row24_traceSegment_066_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 153 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 144 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 144 9 9, g32p_row24_traceSegment_066_0144_0009, g32p_row24_traceSegment_066_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 162 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 162 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 162 9 9, g32p_row24_traceSegment_066_0162_0009, g32p_row24_traceSegment_066_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 144 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 144 18 18, g32p_row24_traceSegment_066_0144_0018, g32p_row24_traceSegment_066_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 180 9 9, g32p_row24_traceSegment_066_0180_0009, g32p_row24_traceSegment_066_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 198 9 9, g32p_row24_traceSegment_066_0198_0009, g32p_row24_traceSegment_066_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 180 18 18, g32p_row24_traceSegment_066_0180_0018, g32p_row24_traceSegment_066_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 144 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 144 36 36, g32p_row24_traceSegment_066_0144_0036, g32p_row24_traceSegment_066_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 216 9 9, g32p_row24_traceSegment_066_0216_0009, g32p_row24_traceSegment_066_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 243 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 234 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 234 9 9, g32p_row24_traceSegment_066_0234_0009, g32p_row24_traceSegment_066_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 216 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 216 18 18, g32p_row24_traceSegment_066_0216_0018, g32p_row24_traceSegment_066_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 252 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 252 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 252 9 9, g32p_row24_traceSegment_066_0252_0009, g32p_row24_traceSegment_066_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 270 9 9, g32p_row24_traceSegment_066_0270_0009, g32p_row24_traceSegment_066_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 252 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 252 18 18, g32p_row24_traceSegment_066_0252_0018, g32p_row24_traceSegment_066_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 216 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 216 36 36, g32p_row24_traceSegment_066_0216_0036, g32p_row24_traceSegment_066_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 144 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 144 72 72, g32p_row24_traceSegment_066_0144_0072, g32p_row24_traceSegment_066_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_066 0 288 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 144 144, g32p_row24_traceSegment_066_0000_0144, g32p_row24_traceSegment_066_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 288 9 9, g32p_row24_traceSegment_066_0288_0009, g32p_row24_traceSegment_066_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 306 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 306 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 306 9 9, g32p_row24_traceSegment_066_0306_0009, g32p_row24_traceSegment_066_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 288 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 288 18 18, g32p_row24_traceSegment_066_0288_0018, g32p_row24_traceSegment_066_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 324 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 333 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 324 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 324 9 9, g32p_row24_traceSegment_066_0324_0009, g32p_row24_traceSegment_066_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 351 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 342 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 342 9 9, g32p_row24_traceSegment_066_0342_0009, g32p_row24_traceSegment_066_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 324 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 324 18 18, g32p_row24_traceSegment_066_0324_0018, g32p_row24_traceSegment_066_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 288 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 288 36 36, g32p_row24_traceSegment_066_0288_0036, g32p_row24_traceSegment_066_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 360 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 360 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 360 9 9, g32p_row24_traceSegment_066_0360_0009, g32p_row24_traceSegment_066_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 378 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 387 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 378 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 378 9 9, g32p_row24_traceSegment_066_0378_0009, g32p_row24_traceSegment_066_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 360 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 360 18 18, g32p_row24_traceSegment_066_0360_0018, g32p_row24_traceSegment_066_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 396 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 396 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 396 9 9, g32p_row24_traceSegment_066_0396_0009, g32p_row24_traceSegment_066_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 414 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 414 9 9, g32p_row24_traceSegment_066_0414_0009, g32p_row24_traceSegment_066_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 396 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 396 18 18, g32p_row24_traceSegment_066_0396_0018, g32p_row24_traceSegment_066_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 360 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 360 36 36, g32p_row24_traceSegment_066_0360_0036, g32p_row24_traceSegment_066_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 288 144 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 288 72 72, g32p_row24_traceSegment_066_0288_0072, g32p_row24_traceSegment_066_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 441 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 432 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 432 9 9, g32p_row24_traceSegment_066_0432_0009, g32p_row24_traceSegment_066_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 450 9 9, g32p_row24_traceSegment_066_0450_0009, g32p_row24_traceSegment_066_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 432 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 432 18 18, g32p_row24_traceSegment_066_0432_0018, g32p_row24_traceSegment_066_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 468 9 9, g32p_row24_traceSegment_066_0468_0009, g32p_row24_traceSegment_066_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 495 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 486 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 486 9 9, g32p_row24_traceSegment_066_0486_0009, g32p_row24_traceSegment_066_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 468 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 468 18 18, g32p_row24_traceSegment_066_0468_0018, g32p_row24_traceSegment_066_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 432 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 432 36 36, g32p_row24_traceSegment_066_0432_0036, g32p_row24_traceSegment_066_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 504 9 9, g32p_row24_traceSegment_066_0504_0009, g32p_row24_traceSegment_066_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 522 9 9, g32p_row24_traceSegment_066_0522_0009, g32p_row24_traceSegment_066_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 504 18 18, g32p_row24_traceSegment_066_0504_0018, g32p_row24_traceSegment_066_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 540 9 9, g32p_row24_traceSegment_066_0540_0009, g32p_row24_traceSegment_066_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 558 9 9, g32p_row24_traceSegment_066_0558_0009, g32p_row24_traceSegment_066_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 540 18 18, g32p_row24_traceSegment_066_0540_0018, g32p_row24_traceSegment_066_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 504 36 36, g32p_row24_traceSegment_066_0504_0036, g32p_row24_traceSegment_066_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 432 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 432 72 72, g32p_row24_traceSegment_066_0432_0072, g32p_row24_traceSegment_066_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_066 288 288 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 288 144 144, g32p_row24_traceSegment_066_0288_0144, g32p_row24_traceSegment_066_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_066 0 576 = [0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 288 288, g32p_row24_traceSegment_066_0000_0288, g32p_row24_traceSegment_066_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 576 9 9, g32p_row24_traceSegment_066_0576_0009, g32p_row24_traceSegment_066_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 594 9 9, g32p_row24_traceSegment_066_0594_0009, g32p_row24_traceSegment_066_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 576 18 18, g32p_row24_traceSegment_066_0576_0018, g32p_row24_traceSegment_066_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 612 9 9, g32p_row24_traceSegment_066_0612_0009, g32p_row24_traceSegment_066_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 630 9 9, g32p_row24_traceSegment_066_0630_0009, g32p_row24_traceSegment_066_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 612 18 18, g32p_row24_traceSegment_066_0612_0018, g32p_row24_traceSegment_066_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 576 36 36, g32p_row24_traceSegment_066_0576_0036, g32p_row24_traceSegment_066_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 648 9 9, g32p_row24_traceSegment_066_0648_0009, g32p_row24_traceSegment_066_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 666 9 9, g32p_row24_traceSegment_066_0666_0009, g32p_row24_traceSegment_066_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 648 18 18, g32p_row24_traceSegment_066_0648_0018, g32p_row24_traceSegment_066_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 684 9 9, g32p_row24_traceSegment_066_0684_0009, g32p_row24_traceSegment_066_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 702 9 9, g32p_row24_traceSegment_066_0702_0009, g32p_row24_traceSegment_066_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 684 18 18, g32p_row24_traceSegment_066_0684_0018, g32p_row24_traceSegment_066_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 648 36 36, g32p_row24_traceSegment_066_0648_0036, g32p_row24_traceSegment_066_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 576 72 72, g32p_row24_traceSegment_066_0576_0072, g32p_row24_traceSegment_066_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 720 9 9, g32p_row24_traceSegment_066_0720_0009, g32p_row24_traceSegment_066_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 738 9 9, g32p_row24_traceSegment_066_0738_0009, g32p_row24_traceSegment_066_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 720 18 18, g32p_row24_traceSegment_066_0720_0018, g32p_row24_traceSegment_066_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 756 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 756 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 756 9 9, g32p_row24_traceSegment_066_0756_0009, g32p_row24_traceSegment_066_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 774 9 9, g32p_row24_traceSegment_066_0774_0009, g32p_row24_traceSegment_066_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 756 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 756 18 18, g32p_row24_traceSegment_066_0756_0018, g32p_row24_traceSegment_066_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 720 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 720 36 36, g32p_row24_traceSegment_066_0720_0036, g32p_row24_traceSegment_066_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 801 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 792 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 792 9 9, g32p_row24_traceSegment_066_0792_0009, g32p_row24_traceSegment_066_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 810 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 810 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 810 9 9, g32p_row24_traceSegment_066_0810_0009, g32p_row24_traceSegment_066_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 792 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 792 18 18, g32p_row24_traceSegment_066_0792_0018, g32p_row24_traceSegment_066_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 828 9 9, g32p_row24_traceSegment_066_0828_0009, g32p_row24_traceSegment_066_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 846 9 9, g32p_row24_traceSegment_066_0846_0009, g32p_row24_traceSegment_066_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 828 18 18, g32p_row24_traceSegment_066_0828_0018, g32p_row24_traceSegment_066_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 792 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 792 36 36, g32p_row24_traceSegment_066_0792_0036, g32p_row24_traceSegment_066_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 720 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 720 72 72, g32p_row24_traceSegment_066_0720_0072, g32p_row24_traceSegment_066_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_066 576 288 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 576 144 144, g32p_row24_traceSegment_066_0576_0144, g32p_row24_traceSegment_066_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 873 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 864 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 864 9 9, g32p_row24_traceSegment_066_0864_0009, g32p_row24_traceSegment_066_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 882 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 882 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 882 9 9, g32p_row24_traceSegment_066_0882_0009, g32p_row24_traceSegment_066_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 864 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 864 18 18, g32p_row24_traceSegment_066_0864_0018, g32p_row24_traceSegment_066_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 900 9 9, g32p_row24_traceSegment_066_0900_0009, g32p_row24_traceSegment_066_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 918 9 9, g32p_row24_traceSegment_066_0918_0009, g32p_row24_traceSegment_066_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 900 18 18, g32p_row24_traceSegment_066_0900_0018, g32p_row24_traceSegment_066_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 864 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 864 36 36, g32p_row24_traceSegment_066_0864_0036, g32p_row24_traceSegment_066_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 936 9 9, g32p_row24_traceSegment_066_0936_0009, g32p_row24_traceSegment_066_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 954 9 9, g32p_row24_traceSegment_066_0954_0009, g32p_row24_traceSegment_066_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 936 18 18, g32p_row24_traceSegment_066_0936_0018, g32p_row24_traceSegment_066_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 972 9 9, g32p_row24_traceSegment_066_0972_0009, g32p_row24_traceSegment_066_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 990 9 9, g32p_row24_traceSegment_066_0990_0009, g32p_row24_traceSegment_066_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 972 18 18, g32p_row24_traceSegment_066_0972_0018, g32p_row24_traceSegment_066_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 936 36 36, g32p_row24_traceSegment_066_0936_0036, g32p_row24_traceSegment_066_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 864 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 864 72 72, g32p_row24_traceSegment_066_0864_0072, g32p_row24_traceSegment_066_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1008 9 9, g32p_row24_traceSegment_066_1008_0009, g32p_row24_traceSegment_066_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1026 9 9, g32p_row24_traceSegment_066_1026_0009, g32p_row24_traceSegment_066_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1008 18 18, g32p_row24_traceSegment_066_1008_0018, g32p_row24_traceSegment_066_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1044 9 9, g32p_row24_traceSegment_066_1044_0009, g32p_row24_traceSegment_066_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1062 9 9, g32p_row24_traceSegment_066_1062_0009, g32p_row24_traceSegment_066_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1044 18 18, g32p_row24_traceSegment_066_1044_0018, g32p_row24_traceSegment_066_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1008 36 36, g32p_row24_traceSegment_066_1008_0036, g32p_row24_traceSegment_066_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1080 9 9, g32p_row24_traceSegment_066_1080_0009, g32p_row24_traceSegment_066_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1098 9 9, g32p_row24_traceSegment_066_1098_0009, g32p_row24_traceSegment_066_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1080 18 18, g32p_row24_traceSegment_066_1080_0018, g32p_row24_traceSegment_066_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1116 9 9, g32p_row24_traceSegment_066_1116_0009, g32p_row24_traceSegment_066_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_066 1143 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_066_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_066 1134 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1134 9 9, g32p_row24_traceSegment_066_1134_0009, g32p_row24_traceSegment_066_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_066 1116 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1116 18 18, g32p_row24_traceSegment_066_1116_0018, g32p_row24_traceSegment_066_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_066 1080 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1080 36 36, g32p_row24_traceSegment_066_1080_0036, g32p_row24_traceSegment_066_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_066_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_066 1008 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 1008 72 72, g32p_row24_traceSegment_066_1008_0072, g32p_row24_traceSegment_066_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_066 864 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 864 144 144, g32p_row24_traceSegment_066_0864_0144, g32p_row24_traceSegment_066_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_066 576 576 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 576 288 288, g32p_row24_traceSegment_066_0576_0288, g32p_row24_traceSegment_066_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_066_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_066 0 1152 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_066 0 576 576, g32p_row24_traceSegment_066_0000_0576, g32p_row24_traceSegment_066_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 66 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_066_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_069_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 0 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 9 9, g32p_row24_traceSegment_069_0000_0009, g32p_row24_traceSegment_069_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 18 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 18 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 18 9 9, g32p_row24_traceSegment_069_0018_0009, g32p_row24_traceSegment_069_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 0 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 18 18, g32p_row24_traceSegment_069_0000_0018, g32p_row24_traceSegment_069_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 36 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 36 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 36 9 9, g32p_row24_traceSegment_069_0036_0009, g32p_row24_traceSegment_069_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 63 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 54 9 9, g32p_row24_traceSegment_069_0054_0009, g32p_row24_traceSegment_069_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 36 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 36 18 18, g32p_row24_traceSegment_069_0036_0018, g32p_row24_traceSegment_069_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 0 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 36 36, g32p_row24_traceSegment_069_0000_0036, g32p_row24_traceSegment_069_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 72 9 9, g32p_row24_traceSegment_069_0072_0009, g32p_row24_traceSegment_069_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 90 9 9, g32p_row24_traceSegment_069_0090_0009, g32p_row24_traceSegment_069_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 72 18 18, g32p_row24_traceSegment_069_0072_0018, g32p_row24_traceSegment_069_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 108 9 9, g32p_row24_traceSegment_069_0108_0009, g32p_row24_traceSegment_069_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 126 9 9, g32p_row24_traceSegment_069_0126_0009, g32p_row24_traceSegment_069_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 108 18 18, g32p_row24_traceSegment_069_0108_0018, g32p_row24_traceSegment_069_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 72 36 36, g32p_row24_traceSegment_069_0072_0036, g32p_row24_traceSegment_069_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 0 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 72 72, g32p_row24_traceSegment_069_0000_0072, g32p_row24_traceSegment_069_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 144 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 144 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 144 9 9, g32p_row24_traceSegment_069_0144_0009, g32p_row24_traceSegment_069_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 162 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 162 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 162 9 9, g32p_row24_traceSegment_069_0162_0009, g32p_row24_traceSegment_069_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 144 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 144 18 18, g32p_row24_traceSegment_069_0144_0018, g32p_row24_traceSegment_069_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 180 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 189 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 180 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 180 9 9, g32p_row24_traceSegment_069_0180_0009, g32p_row24_traceSegment_069_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 198 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 198 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 198 9 9, g32p_row24_traceSegment_069_0198_0009, g32p_row24_traceSegment_069_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 180 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 180 18 18, g32p_row24_traceSegment_069_0180_0018, g32p_row24_traceSegment_069_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 144 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 144 36 36, g32p_row24_traceSegment_069_0144_0036, g32p_row24_traceSegment_069_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 225 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 216 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 216 9 9, g32p_row24_traceSegment_069_0216_0009, g32p_row24_traceSegment_069_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 234 9 9, g32p_row24_traceSegment_069_0234_0009, g32p_row24_traceSegment_069_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 216 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 216 18 18, g32p_row24_traceSegment_069_0216_0018, g32p_row24_traceSegment_069_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 252 9 9, g32p_row24_traceSegment_069_0252_0009, g32p_row24_traceSegment_069_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 270 9 9, g32p_row24_traceSegment_069_0270_0009, g32p_row24_traceSegment_069_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 252 18 18, g32p_row24_traceSegment_069_0252_0018, g32p_row24_traceSegment_069_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 216 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 216 36 36, g32p_row24_traceSegment_069_0216_0036, g32p_row24_traceSegment_069_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 144 144 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 144 72 72, g32p_row24_traceSegment_069_0144_0072, g32p_row24_traceSegment_069_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_069 0 288 = [10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 144 144, g32p_row24_traceSegment_069_0000_0144, g32p_row24_traceSegment_069_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 288 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 288 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 288 9 9, g32p_row24_traceSegment_069_0288_0009, g32p_row24_traceSegment_069_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 306 9 9, g32p_row24_traceSegment_069_0306_0009, g32p_row24_traceSegment_069_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 288 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 288 18 18, g32p_row24_traceSegment_069_0288_0018, g32p_row24_traceSegment_069_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 324 9 9, g32p_row24_traceSegment_069_0324_0009, g32p_row24_traceSegment_069_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 342 9 9, g32p_row24_traceSegment_069_0342_0009, g32p_row24_traceSegment_069_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 324 18 18, g32p_row24_traceSegment_069_0324_0018, g32p_row24_traceSegment_069_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 288 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 288 36 36, g32p_row24_traceSegment_069_0288_0036, g32p_row24_traceSegment_069_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 360 9 9, g32p_row24_traceSegment_069_0360_0009, g32p_row24_traceSegment_069_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 378 9 9, g32p_row24_traceSegment_069_0378_0009, g32p_row24_traceSegment_069_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 360 18 18, g32p_row24_traceSegment_069_0360_0018, g32p_row24_traceSegment_069_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 396 9 9, g32p_row24_traceSegment_069_0396_0009, g32p_row24_traceSegment_069_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 414 9 9, g32p_row24_traceSegment_069_0414_0009, g32p_row24_traceSegment_069_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 396 18 18, g32p_row24_traceSegment_069_0396_0018, g32p_row24_traceSegment_069_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 360 36 36, g32p_row24_traceSegment_069_0360_0036, g32p_row24_traceSegment_069_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 288 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 288 72 72, g32p_row24_traceSegment_069_0288_0072, g32p_row24_traceSegment_069_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 432 9 9, g32p_row24_traceSegment_069_0432_0009, g32p_row24_traceSegment_069_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 459 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 450 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 450 9 9, g32p_row24_traceSegment_069_0450_0009, g32p_row24_traceSegment_069_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 432 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 432 18 18, g32p_row24_traceSegment_069_0432_0018, g32p_row24_traceSegment_069_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 468 9 9, g32p_row24_traceSegment_069_0468_0009, g32p_row24_traceSegment_069_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 486 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 486 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 486 9 9, g32p_row24_traceSegment_069_0486_0009, g32p_row24_traceSegment_069_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 468 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 468 18 18, g32p_row24_traceSegment_069_0468_0018, g32p_row24_traceSegment_069_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 432 72 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 432 36 36, g32p_row24_traceSegment_069_0432_0036, g32p_row24_traceSegment_069_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 504 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 504 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 504 9 9, g32p_row24_traceSegment_069_0504_0009, g32p_row24_traceSegment_069_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 522 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 522 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 522 9 9, g32p_row24_traceSegment_069_0522_0009, g32p_row24_traceSegment_069_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 504 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 504 18 18, g32p_row24_traceSegment_069_0504_0018, g32p_row24_traceSegment_069_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 549 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 540 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 540 9 9, g32p_row24_traceSegment_069_0540_0009, g32p_row24_traceSegment_069_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 567 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 558 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 558 9 9, g32p_row24_traceSegment_069_0558_0009, g32p_row24_traceSegment_069_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 540 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 540 18 18, g32p_row24_traceSegment_069_0540_0018, g32p_row24_traceSegment_069_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 504 72 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 504 36 36, g32p_row24_traceSegment_069_0504_0036, g32p_row24_traceSegment_069_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 432 144 = [6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 432 72 72, g32p_row24_traceSegment_069_0432_0072, g32p_row24_traceSegment_069_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_069 288 288 = [7, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 288 144 144, g32p_row24_traceSegment_069_0288_0144, g32p_row24_traceSegment_069_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_069 0 576 = [17, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 288 288, g32p_row24_traceSegment_069_0000_0288, g32p_row24_traceSegment_069_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 585 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 576 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 576 9 9, g32p_row24_traceSegment_069_0576_0009, g32p_row24_traceSegment_069_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 594 9 9, g32p_row24_traceSegment_069_0594_0009, g32p_row24_traceSegment_069_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 576 18 18, g32p_row24_traceSegment_069_0576_0018, g32p_row24_traceSegment_069_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 612 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 621 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 612 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 612 9 9, g32p_row24_traceSegment_069_0612_0009, g32p_row24_traceSegment_069_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 630 9 9, g32p_row24_traceSegment_069_0630_0009, g32p_row24_traceSegment_069_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 612 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 612 18 18, g32p_row24_traceSegment_069_0612_0018, g32p_row24_traceSegment_069_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 576 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 576 36 36, g32p_row24_traceSegment_069_0576_0036, g32p_row24_traceSegment_069_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 648 9 9, g32p_row24_traceSegment_069_0648_0009, g32p_row24_traceSegment_069_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 666 9 9, g32p_row24_traceSegment_069_0666_0009, g32p_row24_traceSegment_069_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 648 18 18, g32p_row24_traceSegment_069_0648_0018, g32p_row24_traceSegment_069_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 684 9 9, g32p_row24_traceSegment_069_0684_0009, g32p_row24_traceSegment_069_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 702 9 9, g32p_row24_traceSegment_069_0702_0009, g32p_row24_traceSegment_069_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 684 18 18, g32p_row24_traceSegment_069_0684_0018, g32p_row24_traceSegment_069_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 648 36 36, g32p_row24_traceSegment_069_0648_0036, g32p_row24_traceSegment_069_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 576 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 576 72 72, g32p_row24_traceSegment_069_0576_0072, g32p_row24_traceSegment_069_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 720 9 9, g32p_row24_traceSegment_069_0720_0009, g32p_row24_traceSegment_069_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 738 9 9, g32p_row24_traceSegment_069_0738_0009, g32p_row24_traceSegment_069_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 720 18 18, g32p_row24_traceSegment_069_0720_0018, g32p_row24_traceSegment_069_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 765 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 756 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 756 9 9, g32p_row24_traceSegment_069_0756_0009, g32p_row24_traceSegment_069_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 783 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 774 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 774 9 9, g32p_row24_traceSegment_069_0774_0009, g32p_row24_traceSegment_069_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 756 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 756 18 18, g32p_row24_traceSegment_069_0756_0018, g32p_row24_traceSegment_069_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 720 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 720 36 36, g32p_row24_traceSegment_069_0720_0036, g32p_row24_traceSegment_069_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 792 9 9, g32p_row24_traceSegment_069_0792_0009, g32p_row24_traceSegment_069_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 819 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 810 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 810 9 9, g32p_row24_traceSegment_069_0810_0009, g32p_row24_traceSegment_069_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 792 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 792 18 18, g32p_row24_traceSegment_069_0792_0018, g32p_row24_traceSegment_069_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 828 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 837 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 828 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 828 9 9, g32p_row24_traceSegment_069_0828_0009, g32p_row24_traceSegment_069_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 846 9 9, g32p_row24_traceSegment_069_0846_0009, g32p_row24_traceSegment_069_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 828 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 828 18 18, g32p_row24_traceSegment_069_0828_0018, g32p_row24_traceSegment_069_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 792 72 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 792 36 36, g32p_row24_traceSegment_069_0792_0036, g32p_row24_traceSegment_069_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 720 144 = [3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 720 72 72, g32p_row24_traceSegment_069_0720_0072, g32p_row24_traceSegment_069_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_069 576 288 = [6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 576 144 144, g32p_row24_traceSegment_069_0576_0144, g32p_row24_traceSegment_069_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 864 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 873 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 864 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 864 9 9, g32p_row24_traceSegment_069_0864_0009, g32p_row24_traceSegment_069_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 882 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 882 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 882 9 9, g32p_row24_traceSegment_069_0882_0009, g32p_row24_traceSegment_069_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 864 36 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 864 18 18, g32p_row24_traceSegment_069_0864_0018, g32p_row24_traceSegment_069_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 909 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 900 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 900 9 9, g32p_row24_traceSegment_069_0900_0009, g32p_row24_traceSegment_069_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 918 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 918 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 918 9 9, g32p_row24_traceSegment_069_0918_0009, g32p_row24_traceSegment_069_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 900 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 900 18 18, g32p_row24_traceSegment_069_0900_0018, g32p_row24_traceSegment_069_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 864 72 = [3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 864 36 36, g32p_row24_traceSegment_069_0864_0036, g32p_row24_traceSegment_069_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 936 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 945 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 936 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 936 9 9, g32p_row24_traceSegment_069_0936_0009, g32p_row24_traceSegment_069_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 954 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 963 9 = [2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 954 18 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 954 9 9, g32p_row24_traceSegment_069_0954_0009, g32p_row24_traceSegment_069_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 936 36 = [3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 936 18 18, g32p_row24_traceSegment_069_0936_0018, g32p_row24_traceSegment_069_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 972 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 972 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 972 9 9, g32p_row24_traceSegment_069_0972_0009, g32p_row24_traceSegment_069_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 990 9 9, g32p_row24_traceSegment_069_0990_0009, g32p_row24_traceSegment_069_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 972 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 972 18 18, g32p_row24_traceSegment_069_0972_0018, g32p_row24_traceSegment_069_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 936 72 = [4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 936 36 36, g32p_row24_traceSegment_069_0936_0036, g32p_row24_traceSegment_069_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 864 144 = [7, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 864 72 72, g32p_row24_traceSegment_069_0864_0072, g32p_row24_traceSegment_069_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1017 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1008 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1008 9 9, g32p_row24_traceSegment_069_1008_0009, g32p_row24_traceSegment_069_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1035 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1026 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1026 9 9, g32p_row24_traceSegment_069_1026_0009, g32p_row24_traceSegment_069_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 1008 36 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1008 18 18, g32p_row24_traceSegment_069_1008_0018, g32p_row24_traceSegment_069_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1044 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1044 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1044 9 9, g32p_row24_traceSegment_069_1044_0009, g32p_row24_traceSegment_069_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1062 9 9, g32p_row24_traceSegment_069_1062_0009, g32p_row24_traceSegment_069_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 1044 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1044 18 18, g32p_row24_traceSegment_069_1044_0018, g32p_row24_traceSegment_069_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 1008 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1008 36 36, g32p_row24_traceSegment_069_1008_0036, g32p_row24_traceSegment_069_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1080 9 9, g32p_row24_traceSegment_069_1080_0009, g32p_row24_traceSegment_069_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1107 9 = [3, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1098 18 = [3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1098 9 9, g32p_row24_traceSegment_069_1098_0009, g32p_row24_traceSegment_069_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 1080 36 = [3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1080 18 18, g32p_row24_traceSegment_069_1080_0018, g32p_row24_traceSegment_069_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1116 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1125 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1116 18 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1116 9 9, g32p_row24_traceSegment_069_1116_0009, g32p_row24_traceSegment_069_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1134 9 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_069 1143 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_069_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_069 1134 18 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1134 9 9, g32p_row24_traceSegment_069_1134_0009, g32p_row24_traceSegment_069_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_069 1116 36 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1116 18 18, g32p_row24_traceSegment_069_1116_0018, g32p_row24_traceSegment_069_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_069 1080 72 = [4, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1080 36 36, g32p_row24_traceSegment_069_1080_0036, g32p_row24_traceSegment_069_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_069_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_069 1008 144 = [6, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 1008 72 72, g32p_row24_traceSegment_069_1008_0072, g32p_row24_traceSegment_069_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_069 864 288 = [13, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 864 144 144, g32p_row24_traceSegment_069_0864_0144, g32p_row24_traceSegment_069_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_069 576 576 = [19, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 576 288 288, g32p_row24_traceSegment_069_0576_0288, g32p_row24_traceSegment_069_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_069_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_069 0 1152 = [36, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_069 0 576 576, g32p_row24_traceSegment_069_0000_0576, g32p_row24_traceSegment_069_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 69 = [36, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_069_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_071 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 71 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_071_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 9 9, g32p_row24_traceSegment_071_0000_0009, g32p_row24_traceSegment_071_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 18 9 9, g32p_row24_traceSegment_071_0018_0009, g32p_row24_traceSegment_071_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 18 18, g32p_row24_traceSegment_071_0000_0018, g32p_row24_traceSegment_071_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 36 9 9, g32p_row24_traceSegment_071_0036_0009, g32p_row24_traceSegment_071_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 54 9 9, g32p_row24_traceSegment_071_0054_0009, g32p_row24_traceSegment_071_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 36 18 18, g32p_row24_traceSegment_071_0036_0018, g32p_row24_traceSegment_071_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 36 36, g32p_row24_traceSegment_071_0000_0036, g32p_row24_traceSegment_071_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 72 9 9, g32p_row24_traceSegment_071_0072_0009, g32p_row24_traceSegment_071_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 90 9 9, g32p_row24_traceSegment_071_0090_0009, g32p_row24_traceSegment_071_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 72 18 18, g32p_row24_traceSegment_071_0072_0018, g32p_row24_traceSegment_071_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 108 9 9, g32p_row24_traceSegment_071_0108_0009, g32p_row24_traceSegment_071_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 126 9 9, g32p_row24_traceSegment_071_0126_0009, g32p_row24_traceSegment_071_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 108 18 18, g32p_row24_traceSegment_071_0108_0018, g32p_row24_traceSegment_071_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 72 36 36, g32p_row24_traceSegment_071_0072_0036, g32p_row24_traceSegment_071_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 72 72, g32p_row24_traceSegment_071_0000_0072, g32p_row24_traceSegment_071_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 144 9 9, g32p_row24_traceSegment_071_0144_0009, g32p_row24_traceSegment_071_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 162 9 9, g32p_row24_traceSegment_071_0162_0009, g32p_row24_traceSegment_071_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 144 18 18, g32p_row24_traceSegment_071_0144_0018, g32p_row24_traceSegment_071_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 189 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 180 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 180 9 9, g32p_row24_traceSegment_071_0180_0009, g32p_row24_traceSegment_071_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 207 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 198 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 198 9 9, g32p_row24_traceSegment_071_0198_0009, g32p_row24_traceSegment_071_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 180 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 180 18 18, g32p_row24_traceSegment_071_0180_0018, g32p_row24_traceSegment_071_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 144 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 144 36 36, g32p_row24_traceSegment_071_0144_0036, g32p_row24_traceSegment_071_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 216 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 216 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 216 9 9, g32p_row24_traceSegment_071_0216_0009, g32p_row24_traceSegment_071_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 234 9 9, g32p_row24_traceSegment_071_0234_0009, g32p_row24_traceSegment_071_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 216 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 216 18 18, g32p_row24_traceSegment_071_0216_0018, g32p_row24_traceSegment_071_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 261 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 252 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 252 9 9, g32p_row24_traceSegment_071_0252_0009, g32p_row24_traceSegment_071_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 270 9 9, g32p_row24_traceSegment_071_0270_0009, g32p_row24_traceSegment_071_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 252 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 252 18 18, g32p_row24_traceSegment_071_0252_0018, g32p_row24_traceSegment_071_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 216 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 216 36 36, g32p_row24_traceSegment_071_0216_0036, g32p_row24_traceSegment_071_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 144 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 144 72 72, g32p_row24_traceSegment_071_0144_0072, g32p_row24_traceSegment_071_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_071 0 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 144 144, g32p_row24_traceSegment_071_0000_0144, g32p_row24_traceSegment_071_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 288 9 9, g32p_row24_traceSegment_071_0288_0009, g32p_row24_traceSegment_071_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 306 9 9, g32p_row24_traceSegment_071_0306_0009, g32p_row24_traceSegment_071_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 288 18 18, g32p_row24_traceSegment_071_0288_0018, g32p_row24_traceSegment_071_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 324 9 9, g32p_row24_traceSegment_071_0324_0009, g32p_row24_traceSegment_071_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 342 9 9, g32p_row24_traceSegment_071_0342_0009, g32p_row24_traceSegment_071_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 324 18 18, g32p_row24_traceSegment_071_0324_0018, g32p_row24_traceSegment_071_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 288 36 36, g32p_row24_traceSegment_071_0288_0036, g32p_row24_traceSegment_071_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 360 9 9, g32p_row24_traceSegment_071_0360_0009, g32p_row24_traceSegment_071_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 378 9 9, g32p_row24_traceSegment_071_0378_0009, g32p_row24_traceSegment_071_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 360 18 18, g32p_row24_traceSegment_071_0360_0018, g32p_row24_traceSegment_071_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 396 9 9, g32p_row24_traceSegment_071_0396_0009, g32p_row24_traceSegment_071_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 414 9 9, g32p_row24_traceSegment_071_0414_0009, g32p_row24_traceSegment_071_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 396 18 18, g32p_row24_traceSegment_071_0396_0018, g32p_row24_traceSegment_071_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 360 36 36, g32p_row24_traceSegment_071_0360_0036, g32p_row24_traceSegment_071_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 288 72 72, g32p_row24_traceSegment_071_0288_0072, g32p_row24_traceSegment_071_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 432 9 9, g32p_row24_traceSegment_071_0432_0009, g32p_row24_traceSegment_071_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 459 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 450 9 9, g32p_row24_traceSegment_071_0450_0009, g32p_row24_traceSegment_071_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 432 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 432 18 18, g32p_row24_traceSegment_071_0432_0018, g32p_row24_traceSegment_071_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 477 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 468 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 468 9 9, g32p_row24_traceSegment_071_0468_0009, g32p_row24_traceSegment_071_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 495 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 486 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 486 9 9, g32p_row24_traceSegment_071_0486_0009, g32p_row24_traceSegment_071_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 468 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 468 18 18, g32p_row24_traceSegment_071_0468_0018, g32p_row24_traceSegment_071_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 432 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 432 36 36, g32p_row24_traceSegment_071_0432_0036, g32p_row24_traceSegment_071_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 504 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 504 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 504 9 9, g32p_row24_traceSegment_071_0504_0009, g32p_row24_traceSegment_071_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 522 9 9, g32p_row24_traceSegment_071_0522_0009, g32p_row24_traceSegment_071_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 504 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 504 18 18, g32p_row24_traceSegment_071_0504_0018, g32p_row24_traceSegment_071_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 540 9 9, g32p_row24_traceSegment_071_0540_0009, g32p_row24_traceSegment_071_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 567 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 558 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 558 9 9, g32p_row24_traceSegment_071_0558_0009, g32p_row24_traceSegment_071_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 540 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 540 18 18, g32p_row24_traceSegment_071_0540_0018, g32p_row24_traceSegment_071_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 504 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 504 36 36, g32p_row24_traceSegment_071_0504_0036, g32p_row24_traceSegment_071_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 432 144 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 432 72 72, g32p_row24_traceSegment_071_0432_0072, g32p_row24_traceSegment_071_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_071 288 288 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 288 144 144, g32p_row24_traceSegment_071_0288_0144, g32p_row24_traceSegment_071_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_071 0 576 = [9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 288 288, g32p_row24_traceSegment_071_0000_0288, g32p_row24_traceSegment_071_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 576 9 9, g32p_row24_traceSegment_071_0576_0009, g32p_row24_traceSegment_071_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 594 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 594 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 594 9 9, g32p_row24_traceSegment_071_0594_0009, g32p_row24_traceSegment_071_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 576 18 18, g32p_row24_traceSegment_071_0576_0018, g32p_row24_traceSegment_071_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 612 9 9, g32p_row24_traceSegment_071_0612_0009, g32p_row24_traceSegment_071_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 630 9 9, g32p_row24_traceSegment_071_0630_0009, g32p_row24_traceSegment_071_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 612 18 18, g32p_row24_traceSegment_071_0612_0018, g32p_row24_traceSegment_071_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 576 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 576 36 36, g32p_row24_traceSegment_071_0576_0036, g32p_row24_traceSegment_071_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 648 9 9, g32p_row24_traceSegment_071_0648_0009, g32p_row24_traceSegment_071_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 666 9 9, g32p_row24_traceSegment_071_0666_0009, g32p_row24_traceSegment_071_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 648 18 18, g32p_row24_traceSegment_071_0648_0018, g32p_row24_traceSegment_071_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 684 9 9, g32p_row24_traceSegment_071_0684_0009, g32p_row24_traceSegment_071_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 702 9 9, g32p_row24_traceSegment_071_0702_0009, g32p_row24_traceSegment_071_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 684 18 18, g32p_row24_traceSegment_071_0684_0018, g32p_row24_traceSegment_071_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 648 36 36, g32p_row24_traceSegment_071_0648_0036, g32p_row24_traceSegment_071_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 576 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 576 72 72, g32p_row24_traceSegment_071_0576_0072, g32p_row24_traceSegment_071_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 720 9 9, g32p_row24_traceSegment_071_0720_0009, g32p_row24_traceSegment_071_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 738 9 9, g32p_row24_traceSegment_071_0738_0009, g32p_row24_traceSegment_071_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 720 18 18, g32p_row24_traceSegment_071_0720_0018, g32p_row24_traceSegment_071_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 756 9 9, g32p_row24_traceSegment_071_0756_0009, g32p_row24_traceSegment_071_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 774 9 9, g32p_row24_traceSegment_071_0774_0009, g32p_row24_traceSegment_071_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 756 18 18, g32p_row24_traceSegment_071_0756_0018, g32p_row24_traceSegment_071_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 720 36 36, g32p_row24_traceSegment_071_0720_0036, g32p_row24_traceSegment_071_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 792 9 9, g32p_row24_traceSegment_071_0792_0009, g32p_row24_traceSegment_071_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 819 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 810 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 810 9 9, g32p_row24_traceSegment_071_0810_0009, g32p_row24_traceSegment_071_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 792 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 792 18 18, g32p_row24_traceSegment_071_0792_0018, g32p_row24_traceSegment_071_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 828 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 828 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 828 9 9, g32p_row24_traceSegment_071_0828_0009, g32p_row24_traceSegment_071_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 846 9 9, g32p_row24_traceSegment_071_0846_0009, g32p_row24_traceSegment_071_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 828 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 828 18 18, g32p_row24_traceSegment_071_0828_0018, g32p_row24_traceSegment_071_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 792 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 792 36 36, g32p_row24_traceSegment_071_0792_0036, g32p_row24_traceSegment_071_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 720 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 720 72 72, g32p_row24_traceSegment_071_0720_0072, g32p_row24_traceSegment_071_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_071 576 288 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 576 144 144, g32p_row24_traceSegment_071_0576_0144, g32p_row24_traceSegment_071_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 864 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 873 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 864 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 864 9 9, g32p_row24_traceSegment_071_0864_0009, g32p_row24_traceSegment_071_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 882 9 9, g32p_row24_traceSegment_071_0882_0009, g32p_row24_traceSegment_071_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 864 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 864 18 18, g32p_row24_traceSegment_071_0864_0018, g32p_row24_traceSegment_071_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 900 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 909 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 900 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 900 9 9, g32p_row24_traceSegment_071_0900_0009, g32p_row24_traceSegment_071_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 918 9 9, g32p_row24_traceSegment_071_0918_0009, g32p_row24_traceSegment_071_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 900 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 900 18 18, g32p_row24_traceSegment_071_0900_0018, g32p_row24_traceSegment_071_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 864 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 864 36 36, g32p_row24_traceSegment_071_0864_0036, g32p_row24_traceSegment_071_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 936 9 9, g32p_row24_traceSegment_071_0936_0009, g32p_row24_traceSegment_071_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 954 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 963 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 954 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 954 9 9, g32p_row24_traceSegment_071_0954_0009, g32p_row24_traceSegment_071_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 936 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 936 18 18, g32p_row24_traceSegment_071_0936_0018, g32p_row24_traceSegment_071_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 972 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 972 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 972 9 9, g32p_row24_traceSegment_071_0972_0009, g32p_row24_traceSegment_071_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 990 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 990 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 990 9 9, g32p_row24_traceSegment_071_0990_0009, g32p_row24_traceSegment_071_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 972 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 972 18 18, g32p_row24_traceSegment_071_0972_0018, g32p_row24_traceSegment_071_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 936 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 936 36 36, g32p_row24_traceSegment_071_0936_0036, g32p_row24_traceSegment_071_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 864 144 = [9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 864 72 72, g32p_row24_traceSegment_071_0864_0072, g32p_row24_traceSegment_071_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1008 9 9, g32p_row24_traceSegment_071_1008_0009, g32p_row24_traceSegment_071_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1026 9 9, g32p_row24_traceSegment_071_1026_0009, g32p_row24_traceSegment_071_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1008 18 18, g32p_row24_traceSegment_071_1008_0018, g32p_row24_traceSegment_071_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1044 9 9, g32p_row24_traceSegment_071_1044_0009, g32p_row24_traceSegment_071_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1062 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1062 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1062 9 9, g32p_row24_traceSegment_071_1062_0009, g32p_row24_traceSegment_071_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 1044 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1044 18 18, g32p_row24_traceSegment_071_1044_0018, g32p_row24_traceSegment_071_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 1008 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1008 36 36, g32p_row24_traceSegment_071_1008_0036, g32p_row24_traceSegment_071_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1089 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1080 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1080 9 9, g32p_row24_traceSegment_071_1080_0009, g32p_row24_traceSegment_071_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1098 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1107 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1098 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1098 9 9, g32p_row24_traceSegment_071_1098_0009, g32p_row24_traceSegment_071_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 1080 36 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1080 18 18, g32p_row24_traceSegment_071_1080_0018, g32p_row24_traceSegment_071_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1116 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1125 9 = [3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1116 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1116 9 9, g32p_row24_traceSegment_071_1116_0009, g32p_row24_traceSegment_071_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1134 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_071 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_071_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_071 1134 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1134 9 9, g32p_row24_traceSegment_071_1134_0009, g32p_row24_traceSegment_071_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_071 1116 36 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1116 18 18, g32p_row24_traceSegment_071_1116_0018, g32p_row24_traceSegment_071_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_071 1080 72 = [10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1080 36 36, g32p_row24_traceSegment_071_1080_0036, g32p_row24_traceSegment_071_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_071_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_071 1008 144 = [11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 1008 72 72, g32p_row24_traceSegment_071_1008_0072, g32p_row24_traceSegment_071_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_071 864 288 = [20] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 864 144 144, g32p_row24_traceSegment_071_0864_0144, g32p_row24_traceSegment_071_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_071 576 576 = [23] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 576 288 288, g32p_row24_traceSegment_071_0576_0288, g32p_row24_traceSegment_071_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_071_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_071 0 1152 = [32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_071 0 576 576, g32p_row24_traceSegment_071_0000_0576, g32p_row24_traceSegment_071_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 71 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_071_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_075_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 9 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 0 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 9 9, g32p_row24_traceSegment_075_0000_0009, g32p_row24_traceSegment_075_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 18 9 9, g32p_row24_traceSegment_075_0018_0009, g32p_row24_traceSegment_075_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 0 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 18 18, g32p_row24_traceSegment_075_0000_0018, g32p_row24_traceSegment_075_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 36 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 36 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 36 9 9, g32p_row24_traceSegment_075_0036_0009, g32p_row24_traceSegment_075_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 63 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 54 9 9, g32p_row24_traceSegment_075_0054_0009, g32p_row24_traceSegment_075_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 36 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 36 18 18, g32p_row24_traceSegment_075_0036_0018, g32p_row24_traceSegment_075_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 0 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 36 36, g32p_row24_traceSegment_075_0000_0036, g32p_row24_traceSegment_075_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 72 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 72 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 72 9 9, g32p_row24_traceSegment_075_0072_0009, g32p_row24_traceSegment_075_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 90 9 9, g32p_row24_traceSegment_075_0090_0009, g32p_row24_traceSegment_075_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 72 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 72 18 18, g32p_row24_traceSegment_075_0072_0018, g32p_row24_traceSegment_075_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 108 9 9, g32p_row24_traceSegment_075_0108_0009, g32p_row24_traceSegment_075_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 126 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 135 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 126 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 126 9 9, g32p_row24_traceSegment_075_0126_0009, g32p_row24_traceSegment_075_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 108 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 108 18 18, g32p_row24_traceSegment_075_0108_0018, g32p_row24_traceSegment_075_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 72 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 72 36 36, g32p_row24_traceSegment_075_0072_0036, g32p_row24_traceSegment_075_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 0 144 = [8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 72 72, g32p_row24_traceSegment_075_0000_0072, g32p_row24_traceSegment_075_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 144 9 9, g32p_row24_traceSegment_075_0144_0009, g32p_row24_traceSegment_075_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 162 9 9, g32p_row24_traceSegment_075_0162_0009, g32p_row24_traceSegment_075_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 144 18 18, g32p_row24_traceSegment_075_0144_0018, g32p_row24_traceSegment_075_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 180 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 180 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 180 9 9, g32p_row24_traceSegment_075_0180_0009, g32p_row24_traceSegment_075_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 198 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 198 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 198 9 9, g32p_row24_traceSegment_075_0198_0009, g32p_row24_traceSegment_075_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 180 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 180 18 18, g32p_row24_traceSegment_075_0180_0018, g32p_row24_traceSegment_075_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 144 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 144 36 36, g32p_row24_traceSegment_075_0144_0036, g32p_row24_traceSegment_075_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 216 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 216 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 216 9 9, g32p_row24_traceSegment_075_0216_0009, g32p_row24_traceSegment_075_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 234 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 234 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 234 9 9, g32p_row24_traceSegment_075_0234_0009, g32p_row24_traceSegment_075_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 216 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 216 18 18, g32p_row24_traceSegment_075_0216_0018, g32p_row24_traceSegment_075_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 252 9 9, g32p_row24_traceSegment_075_0252_0009, g32p_row24_traceSegment_075_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 270 9 9, g32p_row24_traceSegment_075_0270_0009, g32p_row24_traceSegment_075_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 252 18 18, g32p_row24_traceSegment_075_0252_0018, g32p_row24_traceSegment_075_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 216 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 216 36 36, g32p_row24_traceSegment_075_0216_0036, g32p_row24_traceSegment_075_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 144 144 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 144 72 72, g32p_row24_traceSegment_075_0144_0072, g32p_row24_traceSegment_075_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_075 0 288 = [13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 144 144, g32p_row24_traceSegment_075_0000_0144, g32p_row24_traceSegment_075_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 288 9 9, g32p_row24_traceSegment_075_0288_0009, g32p_row24_traceSegment_075_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 306 9 9, g32p_row24_traceSegment_075_0306_0009, g32p_row24_traceSegment_075_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 288 18 18, g32p_row24_traceSegment_075_0288_0018, g32p_row24_traceSegment_075_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 324 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 324 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 324 9 9, g32p_row24_traceSegment_075_0324_0009, g32p_row24_traceSegment_075_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 342 9 9, g32p_row24_traceSegment_075_0342_0009, g32p_row24_traceSegment_075_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 324 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 324 18 18, g32p_row24_traceSegment_075_0324_0018, g32p_row24_traceSegment_075_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 288 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 288 36 36, g32p_row24_traceSegment_075_0288_0036, g32p_row24_traceSegment_075_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 360 9 9, g32p_row24_traceSegment_075_0360_0009, g32p_row24_traceSegment_075_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 378 9 9, g32p_row24_traceSegment_075_0378_0009, g32p_row24_traceSegment_075_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 360 18 18, g32p_row24_traceSegment_075_0360_0018, g32p_row24_traceSegment_075_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 396 9 9, g32p_row24_traceSegment_075_0396_0009, g32p_row24_traceSegment_075_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 414 9 9, g32p_row24_traceSegment_075_0414_0009, g32p_row24_traceSegment_075_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 396 18 18, g32p_row24_traceSegment_075_0396_0018, g32p_row24_traceSegment_075_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 360 36 36, g32p_row24_traceSegment_075_0360_0036, g32p_row24_traceSegment_075_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 288 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 288 72 72, g32p_row24_traceSegment_075_0288_0072, g32p_row24_traceSegment_075_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 432 9 9, g32p_row24_traceSegment_075_0432_0009, g32p_row24_traceSegment_075_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 450 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 450 9 9, g32p_row24_traceSegment_075_0450_0009, g32p_row24_traceSegment_075_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 432 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 432 18 18, g32p_row24_traceSegment_075_0432_0018, g32p_row24_traceSegment_075_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 468 9 9, g32p_row24_traceSegment_075_0468_0009, g32p_row24_traceSegment_075_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 486 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 495 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 486 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 486 9 9, g32p_row24_traceSegment_075_0486_0009, g32p_row24_traceSegment_075_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 468 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 468 18 18, g32p_row24_traceSegment_075_0468_0018, g32p_row24_traceSegment_075_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 432 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 432 36 36, g32p_row24_traceSegment_075_0432_0036, g32p_row24_traceSegment_075_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 504 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 504 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 504 9 9, g32p_row24_traceSegment_075_0504_0009, g32p_row24_traceSegment_075_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 522 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 531 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 522 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 522 9 9, g32p_row24_traceSegment_075_0522_0009, g32p_row24_traceSegment_075_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 504 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 504 18 18, g32p_row24_traceSegment_075_0504_0018, g32p_row24_traceSegment_075_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 540 9 9, g32p_row24_traceSegment_075_0540_0009, g32p_row24_traceSegment_075_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 558 9 9, g32p_row24_traceSegment_075_0558_0009, g32p_row24_traceSegment_075_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 540 18 18, g32p_row24_traceSegment_075_0540_0018, g32p_row24_traceSegment_075_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 504 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 504 36 36, g32p_row24_traceSegment_075_0504_0036, g32p_row24_traceSegment_075_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 432 144 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 432 72 72, g32p_row24_traceSegment_075_0432_0072, g32p_row24_traceSegment_075_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_075 288 288 = [7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 288 144 144, g32p_row24_traceSegment_075_0288_0144, g32p_row24_traceSegment_075_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_075 0 576 = [20] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 288 288, g32p_row24_traceSegment_075_0000_0288, g32p_row24_traceSegment_075_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 576 9 9, g32p_row24_traceSegment_075_0576_0009, g32p_row24_traceSegment_075_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 603 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 594 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 594 9 9, g32p_row24_traceSegment_075_0594_0009, g32p_row24_traceSegment_075_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 576 18 18, g32p_row24_traceSegment_075_0576_0018, g32p_row24_traceSegment_075_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 612 9 9, g32p_row24_traceSegment_075_0612_0009, g32p_row24_traceSegment_075_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 639 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 630 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 630 9 9, g32p_row24_traceSegment_075_0630_0009, g32p_row24_traceSegment_075_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 612 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 612 18 18, g32p_row24_traceSegment_075_0612_0018, g32p_row24_traceSegment_075_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 576 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 576 36 36, g32p_row24_traceSegment_075_0576_0036, g32p_row24_traceSegment_075_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 648 9 9, g32p_row24_traceSegment_075_0648_0009, g32p_row24_traceSegment_075_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 666 9 9, g32p_row24_traceSegment_075_0666_0009, g32p_row24_traceSegment_075_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 648 18 18, g32p_row24_traceSegment_075_0648_0018, g32p_row24_traceSegment_075_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 684 9 9, g32p_row24_traceSegment_075_0684_0009, g32p_row24_traceSegment_075_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 702 9 9, g32p_row24_traceSegment_075_0702_0009, g32p_row24_traceSegment_075_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 684 18 18, g32p_row24_traceSegment_075_0684_0018, g32p_row24_traceSegment_075_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 648 36 36, g32p_row24_traceSegment_075_0648_0036, g32p_row24_traceSegment_075_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 576 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 576 72 72, g32p_row24_traceSegment_075_0576_0072, g32p_row24_traceSegment_075_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 729 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 720 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 720 9 9, g32p_row24_traceSegment_075_0720_0009, g32p_row24_traceSegment_075_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 738 9 9, g32p_row24_traceSegment_075_0738_0009, g32p_row24_traceSegment_075_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 720 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 720 18 18, g32p_row24_traceSegment_075_0720_0018, g32p_row24_traceSegment_075_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 756 9 9, g32p_row24_traceSegment_075_0756_0009, g32p_row24_traceSegment_075_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 774 9 9, g32p_row24_traceSegment_075_0774_0009, g32p_row24_traceSegment_075_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 756 18 18, g32p_row24_traceSegment_075_0756_0018, g32p_row24_traceSegment_075_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 720 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 720 36 36, g32p_row24_traceSegment_075_0720_0036, g32p_row24_traceSegment_075_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 792 9 9, g32p_row24_traceSegment_075_0792_0009, g32p_row24_traceSegment_075_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 810 9 9, g32p_row24_traceSegment_075_0810_0009, g32p_row24_traceSegment_075_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 792 18 18, g32p_row24_traceSegment_075_0792_0018, g32p_row24_traceSegment_075_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 837 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 828 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 828 9 9, g32p_row24_traceSegment_075_0828_0009, g32p_row24_traceSegment_075_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 855 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 846 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 846 9 9, g32p_row24_traceSegment_075_0846_0009, g32p_row24_traceSegment_075_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 828 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 828 18 18, g32p_row24_traceSegment_075_0828_0018, g32p_row24_traceSegment_075_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 792 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 792 36 36, g32p_row24_traceSegment_075_0792_0036, g32p_row24_traceSegment_075_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 720 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 720 72 72, g32p_row24_traceSegment_075_0720_0072, g32p_row24_traceSegment_075_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_075 576 288 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 576 144 144, g32p_row24_traceSegment_075_0576_0144, g32p_row24_traceSegment_075_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 873 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 864 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 864 9 9, g32p_row24_traceSegment_075_0864_0009, g32p_row24_traceSegment_075_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 891 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 882 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 882 9 9, g32p_row24_traceSegment_075_0882_0009, g32p_row24_traceSegment_075_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 864 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 864 18 18, g32p_row24_traceSegment_075_0864_0018, g32p_row24_traceSegment_075_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 909 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 900 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 900 9 9, g32p_row24_traceSegment_075_0900_0009, g32p_row24_traceSegment_075_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 918 9 9, g32p_row24_traceSegment_075_0918_0009, g32p_row24_traceSegment_075_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 900 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 900 18 18, g32p_row24_traceSegment_075_0900_0018, g32p_row24_traceSegment_075_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 864 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 864 36 36, g32p_row24_traceSegment_075_0864_0036, g32p_row24_traceSegment_075_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 936 9 9, g32p_row24_traceSegment_075_0936_0009, g32p_row24_traceSegment_075_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 954 9 9, g32p_row24_traceSegment_075_0954_0009, g32p_row24_traceSegment_075_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 936 18 18, g32p_row24_traceSegment_075_0936_0018, g32p_row24_traceSegment_075_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 972 9 9, g32p_row24_traceSegment_075_0972_0009, g32p_row24_traceSegment_075_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 990 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 990 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 990 9 9, g32p_row24_traceSegment_075_0990_0009, g32p_row24_traceSegment_075_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 972 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 972 18 18, g32p_row24_traceSegment_075_0972_0018, g32p_row24_traceSegment_075_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 936 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 936 36 36, g32p_row24_traceSegment_075_0936_0036, g32p_row24_traceSegment_075_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 864 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 864 72 72, g32p_row24_traceSegment_075_0864_0072, g32p_row24_traceSegment_075_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1008 9 9, g32p_row24_traceSegment_075_1008_0009, g32p_row24_traceSegment_075_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1026 9 9, g32p_row24_traceSegment_075_1026_0009, g32p_row24_traceSegment_075_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1008 18 18, g32p_row24_traceSegment_075_1008_0018, g32p_row24_traceSegment_075_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1044 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1044 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1044 9 9, g32p_row24_traceSegment_075_1044_0009, g32p_row24_traceSegment_075_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1062 9 9, g32p_row24_traceSegment_075_1062_0009, g32p_row24_traceSegment_075_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 1044 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1044 18 18, g32p_row24_traceSegment_075_1044_0018, g32p_row24_traceSegment_075_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 1008 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1008 36 36, g32p_row24_traceSegment_075_1008_0036, g32p_row24_traceSegment_075_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1080 9 9, g32p_row24_traceSegment_075_1080_0009, g32p_row24_traceSegment_075_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1107 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1098 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1098 9 9, g32p_row24_traceSegment_075_1098_0009, g32p_row24_traceSegment_075_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 1080 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1080 18 18, g32p_row24_traceSegment_075_1080_0018, g32p_row24_traceSegment_075_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1116 9 9, g32p_row24_traceSegment_075_1116_0009, g32p_row24_traceSegment_075_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_075 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_075_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_075 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1134 9 9, g32p_row24_traceSegment_075_1134_0009, g32p_row24_traceSegment_075_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_075 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1116 18 18, g32p_row24_traceSegment_075_1116_0018, g32p_row24_traceSegment_075_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_075 1080 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1080 36 36, g32p_row24_traceSegment_075_1080_0036, g32p_row24_traceSegment_075_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_075_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_075 1008 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 1008 72 72, g32p_row24_traceSegment_075_1008_0072, g32p_row24_traceSegment_075_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_075 864 288 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 864 144 144, g32p_row24_traceSegment_075_0864_0144, g32p_row24_traceSegment_075_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_075 576 576 = [12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 576 288 288, g32p_row24_traceSegment_075_0576_0288, g32p_row24_traceSegment_075_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_075_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_075 0 1152 = [32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_075 0 576 576, g32p_row24_traceSegment_075_0000_0576, g32p_row24_traceSegment_075_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 75 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_075_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_082_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 9 9, g32p_row24_traceSegment_082_0000_0009, g32p_row24_traceSegment_082_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 18 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 27 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 18 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 18 9 9, g32p_row24_traceSegment_082_0018_0009, g32p_row24_traceSegment_082_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 0 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 18 18, g32p_row24_traceSegment_082_0000_0018, g32p_row24_traceSegment_082_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 36 9 9, g32p_row24_traceSegment_082_0036_0009, g32p_row24_traceSegment_082_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 54 9 9, g32p_row24_traceSegment_082_0054_0009, g32p_row24_traceSegment_082_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 36 18 18, g32p_row24_traceSegment_082_0036_0018, g32p_row24_traceSegment_082_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 0 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 36 36, g32p_row24_traceSegment_082_0000_0036, g32p_row24_traceSegment_082_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 72 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 81 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 72 18 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 72 9 9, g32p_row24_traceSegment_082_0072_0009, g32p_row24_traceSegment_082_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 99 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 90 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 90 9 9, g32p_row24_traceSegment_082_0090_0009, g32p_row24_traceSegment_082_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 72 36 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 72 18 18, g32p_row24_traceSegment_082_0072_0018, g32p_row24_traceSegment_082_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 108 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 108 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 108 9 9, g32p_row24_traceSegment_082_0108_0009, g32p_row24_traceSegment_082_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 126 9 9, g32p_row24_traceSegment_082_0126_0009, g32p_row24_traceSegment_082_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 108 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 108 18 18, g32p_row24_traceSegment_082_0108_0018, g32p_row24_traceSegment_082_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 72 72 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 72 36 36, g32p_row24_traceSegment_082_0072_0036, g32p_row24_traceSegment_082_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 0 144 = [0, 0, 1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 72 72, g32p_row24_traceSegment_082_0000_0072, g32p_row24_traceSegment_082_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 144 9 9, g32p_row24_traceSegment_082_0144_0009, g32p_row24_traceSegment_082_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 162 9 9, g32p_row24_traceSegment_082_0162_0009, g32p_row24_traceSegment_082_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 144 18 18, g32p_row24_traceSegment_082_0144_0018, g32p_row24_traceSegment_082_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 180 9 9, g32p_row24_traceSegment_082_0180_0009, g32p_row24_traceSegment_082_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 207 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 198 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 198 9 9, g32p_row24_traceSegment_082_0198_0009, g32p_row24_traceSegment_082_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 180 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 180 18 18, g32p_row24_traceSegment_082_0180_0018, g32p_row24_traceSegment_082_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 144 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 144 36 36, g32p_row24_traceSegment_082_0144_0036, g32p_row24_traceSegment_082_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 216 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 225 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 216 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 216 9 9, g32p_row24_traceSegment_082_0216_0009, g32p_row24_traceSegment_082_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 243 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 234 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 234 9 9, g32p_row24_traceSegment_082_0234_0009, g32p_row24_traceSegment_082_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 216 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 216 18 18, g32p_row24_traceSegment_082_0216_0018, g32p_row24_traceSegment_082_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 261 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 252 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 252 9 9, g32p_row24_traceSegment_082_0252_0009, g32p_row24_traceSegment_082_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 279 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 270 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 270 9 9, g32p_row24_traceSegment_082_0270_0009, g32p_row24_traceSegment_082_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 252 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 252 18 18, g32p_row24_traceSegment_082_0252_0018, g32p_row24_traceSegment_082_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 216 72 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 216 36 36, g32p_row24_traceSegment_082_0216_0036, g32p_row24_traceSegment_082_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 144 144 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 144 72 72, g32p_row24_traceSegment_082_0144_0072, g32p_row24_traceSegment_082_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_082 0 288 = [0, 0, 1, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 144 144, g32p_row24_traceSegment_082_0000_0144, g32p_row24_traceSegment_082_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 297 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 288 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 288 9 9, g32p_row24_traceSegment_082_0288_0009, g32p_row24_traceSegment_082_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 315 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 306 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 306 9 9, g32p_row24_traceSegment_082_0306_0009, g32p_row24_traceSegment_082_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 288 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 288 18 18, g32p_row24_traceSegment_082_0288_0018, g32p_row24_traceSegment_082_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 324 9 9, g32p_row24_traceSegment_082_0324_0009, g32p_row24_traceSegment_082_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 342 9 9, g32p_row24_traceSegment_082_0342_0009, g32p_row24_traceSegment_082_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 324 18 18, g32p_row24_traceSegment_082_0324_0018, g32p_row24_traceSegment_082_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 288 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 288 36 36, g32p_row24_traceSegment_082_0288_0036, g32p_row24_traceSegment_082_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 369 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 360 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 360 9 9, g32p_row24_traceSegment_082_0360_0009, g32p_row24_traceSegment_082_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 378 9 9, g32p_row24_traceSegment_082_0378_0009, g32p_row24_traceSegment_082_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 360 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 360 18 18, g32p_row24_traceSegment_082_0360_0018, g32p_row24_traceSegment_082_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 396 9 9, g32p_row24_traceSegment_082_0396_0009, g32p_row24_traceSegment_082_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 414 9 9, g32p_row24_traceSegment_082_0414_0009, g32p_row24_traceSegment_082_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 396 18 18, g32p_row24_traceSegment_082_0396_0018, g32p_row24_traceSegment_082_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 360 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 360 36 36, g32p_row24_traceSegment_082_0360_0036, g32p_row24_traceSegment_082_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 288 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 288 72 72, g32p_row24_traceSegment_082_0288_0072, g32p_row24_traceSegment_082_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 432 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 432 9 9, g32p_row24_traceSegment_082_0432_0009, g32p_row24_traceSegment_082_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 450 9 9, g32p_row24_traceSegment_082_0450_0009, g32p_row24_traceSegment_082_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 432 18 18, g32p_row24_traceSegment_082_0432_0018, g32p_row24_traceSegment_082_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 468 9 9, g32p_row24_traceSegment_082_0468_0009, g32p_row24_traceSegment_082_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 486 9 9, g32p_row24_traceSegment_082_0486_0009, g32p_row24_traceSegment_082_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 468 18 18, g32p_row24_traceSegment_082_0468_0018, g32p_row24_traceSegment_082_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 432 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 432 36 36, g32p_row24_traceSegment_082_0432_0036, g32p_row24_traceSegment_082_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 504 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 504 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 504 9 9, g32p_row24_traceSegment_082_0504_0009, g32p_row24_traceSegment_082_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 531 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 522 9 9, g32p_row24_traceSegment_082_0522_0009, g32p_row24_traceSegment_082_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 504 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 504 18 18, g32p_row24_traceSegment_082_0504_0018, g32p_row24_traceSegment_082_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 540 9 9, g32p_row24_traceSegment_082_0540_0009, g32p_row24_traceSegment_082_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 558 9 9, g32p_row24_traceSegment_082_0558_0009, g32p_row24_traceSegment_082_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 540 18 18, g32p_row24_traceSegment_082_0540_0018, g32p_row24_traceSegment_082_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 504 72 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 504 36 36, g32p_row24_traceSegment_082_0504_0036, g32p_row24_traceSegment_082_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 432 144 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 432 72 72, g32p_row24_traceSegment_082_0432_0072, g32p_row24_traceSegment_082_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_082 288 288 = [0, 0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 288 144 144, g32p_row24_traceSegment_082_0288_0144, g32p_row24_traceSegment_082_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_082 0 576 = [0, 0, 2, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 288 288, g32p_row24_traceSegment_082_0000_0288, g32p_row24_traceSegment_082_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 576 9 9, g32p_row24_traceSegment_082_0576_0009, g32p_row24_traceSegment_082_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 594 9 9, g32p_row24_traceSegment_082_0594_0009, g32p_row24_traceSegment_082_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 576 18 18, g32p_row24_traceSegment_082_0576_0018, g32p_row24_traceSegment_082_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 612 9 9, g32p_row24_traceSegment_082_0612_0009, g32p_row24_traceSegment_082_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 630 9 9, g32p_row24_traceSegment_082_0630_0009, g32p_row24_traceSegment_082_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 612 18 18, g32p_row24_traceSegment_082_0612_0018, g32p_row24_traceSegment_082_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 576 36 36, g32p_row24_traceSegment_082_0576_0036, g32p_row24_traceSegment_082_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 648 9 9, g32p_row24_traceSegment_082_0648_0009, g32p_row24_traceSegment_082_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 666 9 9, g32p_row24_traceSegment_082_0666_0009, g32p_row24_traceSegment_082_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 648 18 18, g32p_row24_traceSegment_082_0648_0018, g32p_row24_traceSegment_082_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 684 9 9, g32p_row24_traceSegment_082_0684_0009, g32p_row24_traceSegment_082_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 702 9 9, g32p_row24_traceSegment_082_0702_0009, g32p_row24_traceSegment_082_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 684 18 18, g32p_row24_traceSegment_082_0684_0018, g32p_row24_traceSegment_082_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 648 36 36, g32p_row24_traceSegment_082_0648_0036, g32p_row24_traceSegment_082_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 576 72 72, g32p_row24_traceSegment_082_0576_0072, g32p_row24_traceSegment_082_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 720 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 729 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 720 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 720 9 9, g32p_row24_traceSegment_082_0720_0009, g32p_row24_traceSegment_082_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 738 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 738 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 738 9 9, g32p_row24_traceSegment_082_0738_0009, g32p_row24_traceSegment_082_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 720 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 720 18 18, g32p_row24_traceSegment_082_0720_0018, g32p_row24_traceSegment_082_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 756 9 9, g32p_row24_traceSegment_082_0756_0009, g32p_row24_traceSegment_082_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 774 9 9, g32p_row24_traceSegment_082_0774_0009, g32p_row24_traceSegment_082_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 756 18 18, g32p_row24_traceSegment_082_0756_0018, g32p_row24_traceSegment_082_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 720 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 720 36 36, g32p_row24_traceSegment_082_0720_0036, g32p_row24_traceSegment_082_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 792 9 9, g32p_row24_traceSegment_082_0792_0009, g32p_row24_traceSegment_082_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 810 9 9, g32p_row24_traceSegment_082_0810_0009, g32p_row24_traceSegment_082_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 792 18 18, g32p_row24_traceSegment_082_0792_0018, g32p_row24_traceSegment_082_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 828 9 9, g32p_row24_traceSegment_082_0828_0009, g32p_row24_traceSegment_082_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 846 9 9, g32p_row24_traceSegment_082_0846_0009, g32p_row24_traceSegment_082_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 828 18 18, g32p_row24_traceSegment_082_0828_0018, g32p_row24_traceSegment_082_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 792 36 36, g32p_row24_traceSegment_082_0792_0036, g32p_row24_traceSegment_082_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 720 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 720 72 72, g32p_row24_traceSegment_082_0720_0072, g32p_row24_traceSegment_082_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_082 576 288 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 576 144 144, g32p_row24_traceSegment_082_0576_0144, g32p_row24_traceSegment_082_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 864 9 9, g32p_row24_traceSegment_082_0864_0009, g32p_row24_traceSegment_082_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 882 9 9, g32p_row24_traceSegment_082_0882_0009, g32p_row24_traceSegment_082_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 864 18 18, g32p_row24_traceSegment_082_0864_0018, g32p_row24_traceSegment_082_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 900 9 9, g32p_row24_traceSegment_082_0900_0009, g32p_row24_traceSegment_082_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 918 9 9, g32p_row24_traceSegment_082_0918_0009, g32p_row24_traceSegment_082_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 900 18 18, g32p_row24_traceSegment_082_0900_0018, g32p_row24_traceSegment_082_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 864 36 36, g32p_row24_traceSegment_082_0864_0036, g32p_row24_traceSegment_082_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 936 9 9, g32p_row24_traceSegment_082_0936_0009, g32p_row24_traceSegment_082_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 954 9 9, g32p_row24_traceSegment_082_0954_0009, g32p_row24_traceSegment_082_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 936 18 18, g32p_row24_traceSegment_082_0936_0018, g32p_row24_traceSegment_082_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 972 9 9, g32p_row24_traceSegment_082_0972_0009, g32p_row24_traceSegment_082_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 990 9 9, g32p_row24_traceSegment_082_0990_0009, g32p_row24_traceSegment_082_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 972 18 18, g32p_row24_traceSegment_082_0972_0018, g32p_row24_traceSegment_082_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 936 36 36, g32p_row24_traceSegment_082_0936_0036, g32p_row24_traceSegment_082_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 864 72 72, g32p_row24_traceSegment_082_0864_0072, g32p_row24_traceSegment_082_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1017 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1008 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1008 9 9, g32p_row24_traceSegment_082_1008_0009, g32p_row24_traceSegment_082_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1026 9 9, g32p_row24_traceSegment_082_1026_0009, g32p_row24_traceSegment_082_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 1008 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1008 18 18, g32p_row24_traceSegment_082_1008_0018, g32p_row24_traceSegment_082_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1044 9 9, g32p_row24_traceSegment_082_1044_0009, g32p_row24_traceSegment_082_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1062 9 9, g32p_row24_traceSegment_082_1062_0009, g32p_row24_traceSegment_082_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1044 18 18, g32p_row24_traceSegment_082_1044_0018, g32p_row24_traceSegment_082_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 1008 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1008 36 36, g32p_row24_traceSegment_082_1008_0036, g32p_row24_traceSegment_082_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1080 9 9, g32p_row24_traceSegment_082_1080_0009, g32p_row24_traceSegment_082_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1098 9 9, g32p_row24_traceSegment_082_1098_0009, g32p_row24_traceSegment_082_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1080 18 18, g32p_row24_traceSegment_082_1080_0018, g32p_row24_traceSegment_082_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1116 9 9, g32p_row24_traceSegment_082_1116_0009, g32p_row24_traceSegment_082_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_082 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_082_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_082 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1134 9 9, g32p_row24_traceSegment_082_1134_0009, g32p_row24_traceSegment_082_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_082 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1116 18 18, g32p_row24_traceSegment_082_1116_0018, g32p_row24_traceSegment_082_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_082 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1080 36 36, g32p_row24_traceSegment_082_1080_0036, g32p_row24_traceSegment_082_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_082_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_082 1008 144 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 1008 72 72, g32p_row24_traceSegment_082_1008_0072, g32p_row24_traceSegment_082_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_082 864 288 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 864 144 144, g32p_row24_traceSegment_082_0864_0144, g32p_row24_traceSegment_082_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_082 576 576 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 576 288 288, g32p_row24_traceSegment_082_0576_0288, g32p_row24_traceSegment_082_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_082_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_082 0 1152 = [0, 0, 2, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_082 0 576 576, g32p_row24_traceSegment_082_0000_0576, g32p_row24_traceSegment_082_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 82 = [0, 0, 2, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_082_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row24_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 52) (g32p_literalTraceValue 23 52)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_052]
  decide +kernel

theorem g32p_row24_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 57) (g32p_literalTraceValue 23 57)
      [1, -1, 1] [-3456] = true := by
  rw [g32p_row24_traceCoefficients_057]
  decide +kernel

theorem g32p_row24_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 65) (g32p_literalTraceValue 23 65)
      [1, -1, 1] [-38016, 3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_065]
  decide +kernel

theorem g32p_row24_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 66) (g32p_literalTraceValue 23 66)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_066]
  decide +kernel

theorem g32p_row24_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 69) (g32p_literalTraceValue 23 69)
      [1, -1, 1] [6912, 6912] = true := by
  rw [g32p_row24_traceCoefficients_069]
  decide +kernel

theorem g32p_row24_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 71) (g32p_literalTraceValue 23 71)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_071]
  decide +kernel

theorem g32p_row24_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 75) (g32p_literalTraceValue 23 75)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_075]
  decide +kernel

theorem g32p_row24_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 82) (g32p_literalTraceValue 23 82)
      [1, -1, 1] [0, 0, 41472, 41472] = true := by
  rw [g32p_row24_traceCoefficients_082]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
