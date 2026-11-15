import HodgeLean.Foundations.Program.G32PropFourSixPacked0393
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0394
import HodgeLean.Foundations.Program.G32PropFourSixPacked0395
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_083 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 83 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_083_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 9 9, g32p_row24_traceSegment_083_0000_0009, g32p_row24_traceSegment_083_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 18 9 9, g32p_row24_traceSegment_083_0018_0009, g32p_row24_traceSegment_083_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 18 18, g32p_row24_traceSegment_083_0000_0018, g32p_row24_traceSegment_083_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 36 9 9, g32p_row24_traceSegment_083_0036_0009, g32p_row24_traceSegment_083_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 54 9 9, g32p_row24_traceSegment_083_0054_0009, g32p_row24_traceSegment_083_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 36 18 18, g32p_row24_traceSegment_083_0036_0018, g32p_row24_traceSegment_083_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 36 36, g32p_row24_traceSegment_083_0000_0036, g32p_row24_traceSegment_083_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 72 9 9, g32p_row24_traceSegment_083_0072_0009, g32p_row24_traceSegment_083_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 90 9 9, g32p_row24_traceSegment_083_0090_0009, g32p_row24_traceSegment_083_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 72 18 18, g32p_row24_traceSegment_083_0072_0018, g32p_row24_traceSegment_083_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 108 9 9, g32p_row24_traceSegment_083_0108_0009, g32p_row24_traceSegment_083_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 126 9 9, g32p_row24_traceSegment_083_0126_0009, g32p_row24_traceSegment_083_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 108 18 18, g32p_row24_traceSegment_083_0108_0018, g32p_row24_traceSegment_083_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 72 36 36, g32p_row24_traceSegment_083_0072_0036, g32p_row24_traceSegment_083_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 72 72, g32p_row24_traceSegment_083_0000_0072, g32p_row24_traceSegment_083_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 144 9 9, g32p_row24_traceSegment_083_0144_0009, g32p_row24_traceSegment_083_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 162 9 9, g32p_row24_traceSegment_083_0162_0009, g32p_row24_traceSegment_083_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 144 18 18, g32p_row24_traceSegment_083_0144_0018, g32p_row24_traceSegment_083_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 180 9 9, g32p_row24_traceSegment_083_0180_0009, g32p_row24_traceSegment_083_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 198 9 9, g32p_row24_traceSegment_083_0198_0009, g32p_row24_traceSegment_083_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 180 18 18, g32p_row24_traceSegment_083_0180_0018, g32p_row24_traceSegment_083_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 144 36 36, g32p_row24_traceSegment_083_0144_0036, g32p_row24_traceSegment_083_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 216 9 9, g32p_row24_traceSegment_083_0216_0009, g32p_row24_traceSegment_083_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 234 9 9, g32p_row24_traceSegment_083_0234_0009, g32p_row24_traceSegment_083_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 216 18 18, g32p_row24_traceSegment_083_0216_0018, g32p_row24_traceSegment_083_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 261 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 252 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 252 9 9, g32p_row24_traceSegment_083_0252_0009, g32p_row24_traceSegment_083_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 279 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 270 9 9, g32p_row24_traceSegment_083_0270_0009, g32p_row24_traceSegment_083_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 252 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 252 18 18, g32p_row24_traceSegment_083_0252_0018, g32p_row24_traceSegment_083_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 216 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 216 36 36, g32p_row24_traceSegment_083_0216_0036, g32p_row24_traceSegment_083_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 144 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 144 72 72, g32p_row24_traceSegment_083_0144_0072, g32p_row24_traceSegment_083_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_083 0 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 144 144, g32p_row24_traceSegment_083_0000_0144, g32p_row24_traceSegment_083_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 288 9 9, g32p_row24_traceSegment_083_0288_0009, g32p_row24_traceSegment_083_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 306 9 9, g32p_row24_traceSegment_083_0306_0009, g32p_row24_traceSegment_083_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 288 18 18, g32p_row24_traceSegment_083_0288_0018, g32p_row24_traceSegment_083_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 324 9 9, g32p_row24_traceSegment_083_0324_0009, g32p_row24_traceSegment_083_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 342 9 9, g32p_row24_traceSegment_083_0342_0009, g32p_row24_traceSegment_083_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 324 18 18, g32p_row24_traceSegment_083_0324_0018, g32p_row24_traceSegment_083_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 288 36 36, g32p_row24_traceSegment_083_0288_0036, g32p_row24_traceSegment_083_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 360 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 360 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 360 9 9, g32p_row24_traceSegment_083_0360_0009, g32p_row24_traceSegment_083_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 378 9 9, g32p_row24_traceSegment_083_0378_0009, g32p_row24_traceSegment_083_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 360 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 360 18 18, g32p_row24_traceSegment_083_0360_0018, g32p_row24_traceSegment_083_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 396 9 9, g32p_row24_traceSegment_083_0396_0009, g32p_row24_traceSegment_083_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 414 9 9, g32p_row24_traceSegment_083_0414_0009, g32p_row24_traceSegment_083_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 396 18 18, g32p_row24_traceSegment_083_0396_0018, g32p_row24_traceSegment_083_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 360 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 360 36 36, g32p_row24_traceSegment_083_0360_0036, g32p_row24_traceSegment_083_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 288 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 288 72 72, g32p_row24_traceSegment_083_0288_0072, g32p_row24_traceSegment_083_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 432 9 9, g32p_row24_traceSegment_083_0432_0009, g32p_row24_traceSegment_083_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 450 9 9, g32p_row24_traceSegment_083_0450_0009, g32p_row24_traceSegment_083_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 432 18 18, g32p_row24_traceSegment_083_0432_0018, g32p_row24_traceSegment_083_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 468 9 9, g32p_row24_traceSegment_083_0468_0009, g32p_row24_traceSegment_083_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 486 9 9, g32p_row24_traceSegment_083_0486_0009, g32p_row24_traceSegment_083_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 468 18 18, g32p_row24_traceSegment_083_0468_0018, g32p_row24_traceSegment_083_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 432 36 36, g32p_row24_traceSegment_083_0432_0036, g32p_row24_traceSegment_083_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 504 9 9, g32p_row24_traceSegment_083_0504_0009, g32p_row24_traceSegment_083_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 522 9 9, g32p_row24_traceSegment_083_0522_0009, g32p_row24_traceSegment_083_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 504 18 18, g32p_row24_traceSegment_083_0504_0018, g32p_row24_traceSegment_083_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 540 9 9, g32p_row24_traceSegment_083_0540_0009, g32p_row24_traceSegment_083_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 558 9 9, g32p_row24_traceSegment_083_0558_0009, g32p_row24_traceSegment_083_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 540 18 18, g32p_row24_traceSegment_083_0540_0018, g32p_row24_traceSegment_083_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 504 36 36, g32p_row24_traceSegment_083_0504_0036, g32p_row24_traceSegment_083_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 432 72 72, g32p_row24_traceSegment_083_0432_0072, g32p_row24_traceSegment_083_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_083 288 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 288 144 144, g32p_row24_traceSegment_083_0288_0144, g32p_row24_traceSegment_083_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_083 0 576 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 288 288, g32p_row24_traceSegment_083_0000_0288, g32p_row24_traceSegment_083_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 576 9 9, g32p_row24_traceSegment_083_0576_0009, g32p_row24_traceSegment_083_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 603 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 594 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 594 9 9, g32p_row24_traceSegment_083_0594_0009, g32p_row24_traceSegment_083_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 576 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 576 18 18, g32p_row24_traceSegment_083_0576_0018, g32p_row24_traceSegment_083_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 612 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 612 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 612 9 9, g32p_row24_traceSegment_083_0612_0009, g32p_row24_traceSegment_083_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 630 9 9, g32p_row24_traceSegment_083_0630_0009, g32p_row24_traceSegment_083_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 612 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 612 18 18, g32p_row24_traceSegment_083_0612_0018, g32p_row24_traceSegment_083_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 576 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 576 36 36, g32p_row24_traceSegment_083_0576_0036, g32p_row24_traceSegment_083_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 648 9 9, g32p_row24_traceSegment_083_0648_0009, g32p_row24_traceSegment_083_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 675 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 666 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 666 9 9, g32p_row24_traceSegment_083_0666_0009, g32p_row24_traceSegment_083_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 648 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 648 18 18, g32p_row24_traceSegment_083_0648_0018, g32p_row24_traceSegment_083_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 684 9 9, g32p_row24_traceSegment_083_0684_0009, g32p_row24_traceSegment_083_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 702 9 9, g32p_row24_traceSegment_083_0702_0009, g32p_row24_traceSegment_083_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 684 18 18, g32p_row24_traceSegment_083_0684_0018, g32p_row24_traceSegment_083_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 648 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 648 36 36, g32p_row24_traceSegment_083_0648_0036, g32p_row24_traceSegment_083_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 576 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 576 72 72, g32p_row24_traceSegment_083_0576_0072, g32p_row24_traceSegment_083_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 720 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 729 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 720 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 720 9 9, g32p_row24_traceSegment_083_0720_0009, g32p_row24_traceSegment_083_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 747 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 738 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 738 9 9, g32p_row24_traceSegment_083_0738_0009, g32p_row24_traceSegment_083_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 720 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 720 18 18, g32p_row24_traceSegment_083_0720_0018, g32p_row24_traceSegment_083_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 756 9 9, g32p_row24_traceSegment_083_0756_0009, g32p_row24_traceSegment_083_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 774 9 9, g32p_row24_traceSegment_083_0774_0009, g32p_row24_traceSegment_083_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 756 18 18, g32p_row24_traceSegment_083_0756_0018, g32p_row24_traceSegment_083_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 720 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 720 36 36, g32p_row24_traceSegment_083_0720_0036, g32p_row24_traceSegment_083_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 792 9 9, g32p_row24_traceSegment_083_0792_0009, g32p_row24_traceSegment_083_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 810 9 9, g32p_row24_traceSegment_083_0810_0009, g32p_row24_traceSegment_083_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 792 18 18, g32p_row24_traceSegment_083_0792_0018, g32p_row24_traceSegment_083_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 828 9 9, g32p_row24_traceSegment_083_0828_0009, g32p_row24_traceSegment_083_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 846 9 9, g32p_row24_traceSegment_083_0846_0009, g32p_row24_traceSegment_083_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 828 18 18, g32p_row24_traceSegment_083_0828_0018, g32p_row24_traceSegment_083_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 792 36 36, g32p_row24_traceSegment_083_0792_0036, g32p_row24_traceSegment_083_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 720 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 720 72 72, g32p_row24_traceSegment_083_0720_0072, g32p_row24_traceSegment_083_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_083 576 288 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 576 144 144, g32p_row24_traceSegment_083_0576_0144, g32p_row24_traceSegment_083_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 864 9 9, g32p_row24_traceSegment_083_0864_0009, g32p_row24_traceSegment_083_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 882 9 9, g32p_row24_traceSegment_083_0882_0009, g32p_row24_traceSegment_083_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 864 18 18, g32p_row24_traceSegment_083_0864_0018, g32p_row24_traceSegment_083_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 900 9 9, g32p_row24_traceSegment_083_0900_0009, g32p_row24_traceSegment_083_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 918 9 9, g32p_row24_traceSegment_083_0918_0009, g32p_row24_traceSegment_083_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 900 18 18, g32p_row24_traceSegment_083_0900_0018, g32p_row24_traceSegment_083_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 864 36 36, g32p_row24_traceSegment_083_0864_0036, g32p_row24_traceSegment_083_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 936 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 936 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 936 9 9, g32p_row24_traceSegment_083_0936_0009, g32p_row24_traceSegment_083_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 954 9 9, g32p_row24_traceSegment_083_0954_0009, g32p_row24_traceSegment_083_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 936 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 936 18 18, g32p_row24_traceSegment_083_0936_0018, g32p_row24_traceSegment_083_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 972 9 9, g32p_row24_traceSegment_083_0972_0009, g32p_row24_traceSegment_083_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 990 9 9, g32p_row24_traceSegment_083_0990_0009, g32p_row24_traceSegment_083_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 972 18 18, g32p_row24_traceSegment_083_0972_0018, g32p_row24_traceSegment_083_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 936 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 936 36 36, g32p_row24_traceSegment_083_0936_0036, g32p_row24_traceSegment_083_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 864 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 864 72 72, g32p_row24_traceSegment_083_0864_0072, g32p_row24_traceSegment_083_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1008 9 9, g32p_row24_traceSegment_083_1008_0009, g32p_row24_traceSegment_083_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1026 9 9, g32p_row24_traceSegment_083_1026_0009, g32p_row24_traceSegment_083_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1008 18 18, g32p_row24_traceSegment_083_1008_0018, g32p_row24_traceSegment_083_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1044 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1044 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1044 9 9, g32p_row24_traceSegment_083_1044_0009, g32p_row24_traceSegment_083_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1062 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1062 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1062 9 9, g32p_row24_traceSegment_083_1062_0009, g32p_row24_traceSegment_083_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 1044 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1044 18 18, g32p_row24_traceSegment_083_1044_0018, g32p_row24_traceSegment_083_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 1008 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1008 36 36, g32p_row24_traceSegment_083_1008_0036, g32p_row24_traceSegment_083_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1080 9 9, g32p_row24_traceSegment_083_1080_0009, g32p_row24_traceSegment_083_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1098 9 9, g32p_row24_traceSegment_083_1098_0009, g32p_row24_traceSegment_083_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1080 18 18, g32p_row24_traceSegment_083_1080_0018, g32p_row24_traceSegment_083_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1116 9 9, g32p_row24_traceSegment_083_1116_0009, g32p_row24_traceSegment_083_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_083 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_083_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_083 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1134 9 9, g32p_row24_traceSegment_083_1134_0009, g32p_row24_traceSegment_083_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_083 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1116 18 18, g32p_row24_traceSegment_083_1116_0018, g32p_row24_traceSegment_083_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_083 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1080 36 36, g32p_row24_traceSegment_083_1080_0036, g32p_row24_traceSegment_083_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_083_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_083 1008 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 1008 72 72, g32p_row24_traceSegment_083_1008_0072, g32p_row24_traceSegment_083_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_083 864 288 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 864 144 144, g32p_row24_traceSegment_083_0864_0144, g32p_row24_traceSegment_083_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_083 576 576 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 576 288 288, g32p_row24_traceSegment_083_0576_0288, g32p_row24_traceSegment_083_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_083_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_083 0 1152 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_083 0 576 576, g32p_row24_traceSegment_083_0000_0576, g32p_row24_traceSegment_083_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 83 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_083_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_084_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 9 9, g32p_row24_traceSegment_084_0000_0009, g32p_row24_traceSegment_084_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 18 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 27 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 18 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 18 9 9, g32p_row24_traceSegment_084_0018_0009, g32p_row24_traceSegment_084_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 0 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 18 18, g32p_row24_traceSegment_084_0000_0018, g32p_row24_traceSegment_084_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 36 9 9, g32p_row24_traceSegment_084_0036_0009, g32p_row24_traceSegment_084_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 54 9 9, g32p_row24_traceSegment_084_0054_0009, g32p_row24_traceSegment_084_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 36 18 18, g32p_row24_traceSegment_084_0036_0018, g32p_row24_traceSegment_084_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 0 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 36 36, g32p_row24_traceSegment_084_0000_0036, g32p_row24_traceSegment_084_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 72 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 72 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 72 9 9, g32p_row24_traceSegment_084_0072_0009, g32p_row24_traceSegment_084_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 90 9 9, g32p_row24_traceSegment_084_0090_0009, g32p_row24_traceSegment_084_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 72 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 72 18 18, g32p_row24_traceSegment_084_0072_0018, g32p_row24_traceSegment_084_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 108 9 9, g32p_row24_traceSegment_084_0108_0009, g32p_row24_traceSegment_084_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 126 9 9, g32p_row24_traceSegment_084_0126_0009, g32p_row24_traceSegment_084_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 108 18 18, g32p_row24_traceSegment_084_0108_0018, g32p_row24_traceSegment_084_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 72 36 36, g32p_row24_traceSegment_084_0072_0036, g32p_row24_traceSegment_084_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 0 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 72 72, g32p_row24_traceSegment_084_0000_0072, g32p_row24_traceSegment_084_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 144 9 9, g32p_row24_traceSegment_084_0144_0009, g32p_row24_traceSegment_084_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 162 9 9, g32p_row24_traceSegment_084_0162_0009, g32p_row24_traceSegment_084_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 144 18 18, g32p_row24_traceSegment_084_0144_0018, g32p_row24_traceSegment_084_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 180 9 9, g32p_row24_traceSegment_084_0180_0009, g32p_row24_traceSegment_084_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 207 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 198 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 198 9 9, g32p_row24_traceSegment_084_0198_0009, g32p_row24_traceSegment_084_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 180 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 180 18 18, g32p_row24_traceSegment_084_0180_0018, g32p_row24_traceSegment_084_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 144 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 144 36 36, g32p_row24_traceSegment_084_0144_0036, g32p_row24_traceSegment_084_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 216 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 225 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 216 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 216 9 9, g32p_row24_traceSegment_084_0216_0009, g32p_row24_traceSegment_084_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 234 9 9, g32p_row24_traceSegment_084_0234_0009, g32p_row24_traceSegment_084_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 216 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 216 18 18, g32p_row24_traceSegment_084_0216_0018, g32p_row24_traceSegment_084_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 252 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 261 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 252 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 252 9 9, g32p_row24_traceSegment_084_0252_0009, g32p_row24_traceSegment_084_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 270 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 279 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 270 18 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 270 9 9, g32p_row24_traceSegment_084_0270_0009, g32p_row24_traceSegment_084_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 252 36 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 252 18 18, g32p_row24_traceSegment_084_0252_0018, g32p_row24_traceSegment_084_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 216 72 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 216 36 36, g32p_row24_traceSegment_084_0216_0036, g32p_row24_traceSegment_084_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 144 144 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 144 72 72, g32p_row24_traceSegment_084_0144_0072, g32p_row24_traceSegment_084_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_084 0 288 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 144 144, g32p_row24_traceSegment_084_0000_0144, g32p_row24_traceSegment_084_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 288 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 288 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 288 9 9, g32p_row24_traceSegment_084_0288_0009, g32p_row24_traceSegment_084_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 315 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 306 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 306 9 9, g32p_row24_traceSegment_084_0306_0009, g32p_row24_traceSegment_084_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 288 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 288 18 18, g32p_row24_traceSegment_084_0288_0018, g32p_row24_traceSegment_084_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 324 9 9, g32p_row24_traceSegment_084_0324_0009, g32p_row24_traceSegment_084_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 342 9 9, g32p_row24_traceSegment_084_0342_0009, g32p_row24_traceSegment_084_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 324 18 18, g32p_row24_traceSegment_084_0324_0018, g32p_row24_traceSegment_084_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 288 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 288 36 36, g32p_row24_traceSegment_084_0288_0036, g32p_row24_traceSegment_084_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 360 9 9, g32p_row24_traceSegment_084_0360_0009, g32p_row24_traceSegment_084_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 378 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 378 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 378 9 9, g32p_row24_traceSegment_084_0378_0009, g32p_row24_traceSegment_084_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 360 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 360 18 18, g32p_row24_traceSegment_084_0360_0018, g32p_row24_traceSegment_084_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 405 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 396 9 9, g32p_row24_traceSegment_084_0396_0009, g32p_row24_traceSegment_084_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 423 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 414 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 414 9 9, g32p_row24_traceSegment_084_0414_0009, g32p_row24_traceSegment_084_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 396 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 396 18 18, g32p_row24_traceSegment_084_0396_0018, g32p_row24_traceSegment_084_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 360 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 360 36 36, g32p_row24_traceSegment_084_0360_0036, g32p_row24_traceSegment_084_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 288 144 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 288 72 72, g32p_row24_traceSegment_084_0288_0072, g32p_row24_traceSegment_084_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 432 9 9, g32p_row24_traceSegment_084_0432_0009, g32p_row24_traceSegment_084_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 450 9 9, g32p_row24_traceSegment_084_0450_0009, g32p_row24_traceSegment_084_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 432 18 18, g32p_row24_traceSegment_084_0432_0018, g32p_row24_traceSegment_084_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 477 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 468 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 468 9 9, g32p_row24_traceSegment_084_0468_0009, g32p_row24_traceSegment_084_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 486 9 9, g32p_row24_traceSegment_084_0486_0009, g32p_row24_traceSegment_084_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 468 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 468 18 18, g32p_row24_traceSegment_084_0468_0018, g32p_row24_traceSegment_084_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 432 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 432 36 36, g32p_row24_traceSegment_084_0432_0036, g32p_row24_traceSegment_084_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 504 9 9, g32p_row24_traceSegment_084_0504_0009, g32p_row24_traceSegment_084_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 531 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 522 9 9, g32p_row24_traceSegment_084_0522_0009, g32p_row24_traceSegment_084_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 504 18 18, g32p_row24_traceSegment_084_0504_0018, g32p_row24_traceSegment_084_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 540 9 9, g32p_row24_traceSegment_084_0540_0009, g32p_row24_traceSegment_084_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 558 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 558 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 558 9 9, g32p_row24_traceSegment_084_0558_0009, g32p_row24_traceSegment_084_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 540 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 540 18 18, g32p_row24_traceSegment_084_0540_0018, g32p_row24_traceSegment_084_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 504 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 504 36 36, g32p_row24_traceSegment_084_0504_0036, g32p_row24_traceSegment_084_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 432 144 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 432 72 72, g32p_row24_traceSegment_084_0432_0072, g32p_row24_traceSegment_084_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_084 288 288 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 288 144 144, g32p_row24_traceSegment_084_0288_0144, g32p_row24_traceSegment_084_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_084 0 576 = [0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 288 288, g32p_row24_traceSegment_084_0000_0288, g32p_row24_traceSegment_084_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 576 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 576 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 576 9 9, g32p_row24_traceSegment_084_0576_0009, g32p_row24_traceSegment_084_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 594 9 9, g32p_row24_traceSegment_084_0594_0009, g32p_row24_traceSegment_084_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 576 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 576 18 18, g32p_row24_traceSegment_084_0576_0018, g32p_row24_traceSegment_084_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 612 9 9, g32p_row24_traceSegment_084_0612_0009, g32p_row24_traceSegment_084_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 630 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 630 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 630 9 9, g32p_row24_traceSegment_084_0630_0009, g32p_row24_traceSegment_084_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 612 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 612 18 18, g32p_row24_traceSegment_084_0612_0018, g32p_row24_traceSegment_084_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 576 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 576 36 36, g32p_row24_traceSegment_084_0576_0036, g32p_row24_traceSegment_084_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 648 9 9, g32p_row24_traceSegment_084_0648_0009, g32p_row24_traceSegment_084_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 666 9 9, g32p_row24_traceSegment_084_0666_0009, g32p_row24_traceSegment_084_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 648 18 18, g32p_row24_traceSegment_084_0648_0018, g32p_row24_traceSegment_084_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 684 9 9, g32p_row24_traceSegment_084_0684_0009, g32p_row24_traceSegment_084_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 702 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 711 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 702 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 702 9 9, g32p_row24_traceSegment_084_0702_0009, g32p_row24_traceSegment_084_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 684 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 684 18 18, g32p_row24_traceSegment_084_0684_0018, g32p_row24_traceSegment_084_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 648 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 648 36 36, g32p_row24_traceSegment_084_0648_0036, g32p_row24_traceSegment_084_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 576 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 576 72 72, g32p_row24_traceSegment_084_0576_0072, g32p_row24_traceSegment_084_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 720 9 9, g32p_row24_traceSegment_084_0720_0009, g32p_row24_traceSegment_084_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 738 9 9, g32p_row24_traceSegment_084_0738_0009, g32p_row24_traceSegment_084_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 720 18 18, g32p_row24_traceSegment_084_0720_0018, g32p_row24_traceSegment_084_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 756 9 9, g32p_row24_traceSegment_084_0756_0009, g32p_row24_traceSegment_084_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 774 9 9, g32p_row24_traceSegment_084_0774_0009, g32p_row24_traceSegment_084_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 756 18 18, g32p_row24_traceSegment_084_0756_0018, g32p_row24_traceSegment_084_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 720 36 36, g32p_row24_traceSegment_084_0720_0036, g32p_row24_traceSegment_084_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 792 9 9, g32p_row24_traceSegment_084_0792_0009, g32p_row24_traceSegment_084_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 810 9 9, g32p_row24_traceSegment_084_0810_0009, g32p_row24_traceSegment_084_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 792 18 18, g32p_row24_traceSegment_084_0792_0018, g32p_row24_traceSegment_084_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 828 9 9, g32p_row24_traceSegment_084_0828_0009, g32p_row24_traceSegment_084_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 846 9 9, g32p_row24_traceSegment_084_0846_0009, g32p_row24_traceSegment_084_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 828 18 18, g32p_row24_traceSegment_084_0828_0018, g32p_row24_traceSegment_084_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 792 36 36, g32p_row24_traceSegment_084_0792_0036, g32p_row24_traceSegment_084_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 720 72 72, g32p_row24_traceSegment_084_0720_0072, g32p_row24_traceSegment_084_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_084 576 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 576 144 144, g32p_row24_traceSegment_084_0576_0144, g32p_row24_traceSegment_084_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 864 9 9, g32p_row24_traceSegment_084_0864_0009, g32p_row24_traceSegment_084_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 882 9 9, g32p_row24_traceSegment_084_0882_0009, g32p_row24_traceSegment_084_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 864 18 18, g32p_row24_traceSegment_084_0864_0018, g32p_row24_traceSegment_084_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 900 9 9, g32p_row24_traceSegment_084_0900_0009, g32p_row24_traceSegment_084_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 918 9 9, g32p_row24_traceSegment_084_0918_0009, g32p_row24_traceSegment_084_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 900 18 18, g32p_row24_traceSegment_084_0900_0018, g32p_row24_traceSegment_084_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 864 36 36, g32p_row24_traceSegment_084_0864_0036, g32p_row24_traceSegment_084_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 936 9 9, g32p_row24_traceSegment_084_0936_0009, g32p_row24_traceSegment_084_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 954 9 9, g32p_row24_traceSegment_084_0954_0009, g32p_row24_traceSegment_084_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 936 18 18, g32p_row24_traceSegment_084_0936_0018, g32p_row24_traceSegment_084_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 972 9 9, g32p_row24_traceSegment_084_0972_0009, g32p_row24_traceSegment_084_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 990 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 990 9 9, g32p_row24_traceSegment_084_0990_0009, g32p_row24_traceSegment_084_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 972 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 972 18 18, g32p_row24_traceSegment_084_0972_0018, g32p_row24_traceSegment_084_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 936 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 936 36 36, g32p_row24_traceSegment_084_0936_0036, g32p_row24_traceSegment_084_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 864 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 864 72 72, g32p_row24_traceSegment_084_0864_0072, g32p_row24_traceSegment_084_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1008 9 9, g32p_row24_traceSegment_084_1008_0009, g32p_row24_traceSegment_084_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1026 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1026 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1026 9 9, g32p_row24_traceSegment_084_1026_0009, g32p_row24_traceSegment_084_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 1008 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1008 18 18, g32p_row24_traceSegment_084_1008_0018, g32p_row24_traceSegment_084_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1053 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1044 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1044 9 9, g32p_row24_traceSegment_084_1044_0009, g32p_row24_traceSegment_084_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1062 9 9, g32p_row24_traceSegment_084_1062_0009, g32p_row24_traceSegment_084_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 1044 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1044 18 18, g32p_row24_traceSegment_084_1044_0018, g32p_row24_traceSegment_084_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 1008 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1008 36 36, g32p_row24_traceSegment_084_1008_0036, g32p_row24_traceSegment_084_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1080 9 9, g32p_row24_traceSegment_084_1080_0009, g32p_row24_traceSegment_084_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1098 9 9, g32p_row24_traceSegment_084_1098_0009, g32p_row24_traceSegment_084_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1080 18 18, g32p_row24_traceSegment_084_1080_0018, g32p_row24_traceSegment_084_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1116 9 9, g32p_row24_traceSegment_084_1116_0009, g32p_row24_traceSegment_084_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_084 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_084_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_084 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1134 9 9, g32p_row24_traceSegment_084_1134_0009, g32p_row24_traceSegment_084_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_084 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1116 18 18, g32p_row24_traceSegment_084_1116_0018, g32p_row24_traceSegment_084_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_084 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1080 36 36, g32p_row24_traceSegment_084_1080_0036, g32p_row24_traceSegment_084_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_084_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_084 1008 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 1008 72 72, g32p_row24_traceSegment_084_1008_0072, g32p_row24_traceSegment_084_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_084 864 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 864 144 144, g32p_row24_traceSegment_084_0864_0144, g32p_row24_traceSegment_084_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_084 576 576 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 576 288 288, g32p_row24_traceSegment_084_0576_0288, g32p_row24_traceSegment_084_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_084_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_084 0 1152 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_084 0 576 576, g32p_row24_traceSegment_084_0000_0576, g32p_row24_traceSegment_084_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 84 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_084_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_086 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 86 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_086_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 9 9, g32p_row24_traceSegment_086_0000_0009, g32p_row24_traceSegment_086_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 18 9 9, g32p_row24_traceSegment_086_0018_0009, g32p_row24_traceSegment_086_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 18 18, g32p_row24_traceSegment_086_0000_0018, g32p_row24_traceSegment_086_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 36 9 9, g32p_row24_traceSegment_086_0036_0009, g32p_row24_traceSegment_086_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 54 9 9, g32p_row24_traceSegment_086_0054_0009, g32p_row24_traceSegment_086_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 36 18 18, g32p_row24_traceSegment_086_0036_0018, g32p_row24_traceSegment_086_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 36 36, g32p_row24_traceSegment_086_0000_0036, g32p_row24_traceSegment_086_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 81 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 72 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 72 9 9, g32p_row24_traceSegment_086_0072_0009, g32p_row24_traceSegment_086_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 90 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 90 9 9, g32p_row24_traceSegment_086_0090_0009, g32p_row24_traceSegment_086_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 72 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 72 18 18, g32p_row24_traceSegment_086_0072_0018, g32p_row24_traceSegment_086_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 108 9 9, g32p_row24_traceSegment_086_0108_0009, g32p_row24_traceSegment_086_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 126 9 9, g32p_row24_traceSegment_086_0126_0009, g32p_row24_traceSegment_086_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 108 18 18, g32p_row24_traceSegment_086_0108_0018, g32p_row24_traceSegment_086_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 72 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 72 36 36, g32p_row24_traceSegment_086_0072_0036, g32p_row24_traceSegment_086_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 0 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 72 72, g32p_row24_traceSegment_086_0000_0072, g32p_row24_traceSegment_086_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 144 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 144 9 9, g32p_row24_traceSegment_086_0144_0009, g32p_row24_traceSegment_086_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 162 9 9, g32p_row24_traceSegment_086_0162_0009, g32p_row24_traceSegment_086_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 144 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 144 18 18, g32p_row24_traceSegment_086_0144_0018, g32p_row24_traceSegment_086_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 180 9 9, g32p_row24_traceSegment_086_0180_0009, g32p_row24_traceSegment_086_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 198 9 9, g32p_row24_traceSegment_086_0198_0009, g32p_row24_traceSegment_086_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 180 18 18, g32p_row24_traceSegment_086_0180_0018, g32p_row24_traceSegment_086_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 144 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 144 36 36, g32p_row24_traceSegment_086_0144_0036, g32p_row24_traceSegment_086_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 216 9 9, g32p_row24_traceSegment_086_0216_0009, g32p_row24_traceSegment_086_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 234 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 234 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 234 9 9, g32p_row24_traceSegment_086_0234_0009, g32p_row24_traceSegment_086_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 216 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 216 18 18, g32p_row24_traceSegment_086_0216_0018, g32p_row24_traceSegment_086_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 252 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 261 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 252 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 252 9 9, g32p_row24_traceSegment_086_0252_0009, g32p_row24_traceSegment_086_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 270 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 270 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 270 9 9, g32p_row24_traceSegment_086_0270_0009, g32p_row24_traceSegment_086_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 252 36 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 252 18 18, g32p_row24_traceSegment_086_0252_0018, g32p_row24_traceSegment_086_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 216 72 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 216 36 36, g32p_row24_traceSegment_086_0216_0036, g32p_row24_traceSegment_086_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 144 144 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 144 72 72, g32p_row24_traceSegment_086_0144_0072, g32p_row24_traceSegment_086_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_086 0 288 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 144 144, g32p_row24_traceSegment_086_0000_0144, g32p_row24_traceSegment_086_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 288 9 9, g32p_row24_traceSegment_086_0288_0009, g32p_row24_traceSegment_086_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 315 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 306 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 306 9 9, g32p_row24_traceSegment_086_0306_0009, g32p_row24_traceSegment_086_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 288 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 288 18 18, g32p_row24_traceSegment_086_0288_0018, g32p_row24_traceSegment_086_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 324 9 9, g32p_row24_traceSegment_086_0324_0009, g32p_row24_traceSegment_086_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 342 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 342 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 342 9 9, g32p_row24_traceSegment_086_0342_0009, g32p_row24_traceSegment_086_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 324 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 324 18 18, g32p_row24_traceSegment_086_0324_0018, g32p_row24_traceSegment_086_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 288 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 288 36 36, g32p_row24_traceSegment_086_0288_0036, g32p_row24_traceSegment_086_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 369 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 360 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 360 9 9, g32p_row24_traceSegment_086_0360_0009, g32p_row24_traceSegment_086_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 378 9 9, g32p_row24_traceSegment_086_0378_0009, g32p_row24_traceSegment_086_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 360 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 360 18 18, g32p_row24_traceSegment_086_0360_0018, g32p_row24_traceSegment_086_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 396 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 396 9 9, g32p_row24_traceSegment_086_0396_0009, g32p_row24_traceSegment_086_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 414 9 9, g32p_row24_traceSegment_086_0414_0009, g32p_row24_traceSegment_086_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 396 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 396 18 18, g32p_row24_traceSegment_086_0396_0018, g32p_row24_traceSegment_086_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 360 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 360 36 36, g32p_row24_traceSegment_086_0360_0036, g32p_row24_traceSegment_086_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 288 144 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 288 72 72, g32p_row24_traceSegment_086_0288_0072, g32p_row24_traceSegment_086_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 432 9 9, g32p_row24_traceSegment_086_0432_0009, g32p_row24_traceSegment_086_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 450 9 9, g32p_row24_traceSegment_086_0450_0009, g32p_row24_traceSegment_086_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 432 18 18, g32p_row24_traceSegment_086_0432_0018, g32p_row24_traceSegment_086_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 468 9 9, g32p_row24_traceSegment_086_0468_0009, g32p_row24_traceSegment_086_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 486 9 9, g32p_row24_traceSegment_086_0486_0009, g32p_row24_traceSegment_086_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 468 18 18, g32p_row24_traceSegment_086_0468_0018, g32p_row24_traceSegment_086_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 432 36 36, g32p_row24_traceSegment_086_0432_0036, g32p_row24_traceSegment_086_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 504 9 9, g32p_row24_traceSegment_086_0504_0009, g32p_row24_traceSegment_086_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 522 9 9, g32p_row24_traceSegment_086_0522_0009, g32p_row24_traceSegment_086_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 504 18 18, g32p_row24_traceSegment_086_0504_0018, g32p_row24_traceSegment_086_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 540 9 9, g32p_row24_traceSegment_086_0540_0009, g32p_row24_traceSegment_086_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 558 9 9, g32p_row24_traceSegment_086_0558_0009, g32p_row24_traceSegment_086_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 540 18 18, g32p_row24_traceSegment_086_0540_0018, g32p_row24_traceSegment_086_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 504 36 36, g32p_row24_traceSegment_086_0504_0036, g32p_row24_traceSegment_086_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 432 72 72, g32p_row24_traceSegment_086_0432_0072, g32p_row24_traceSegment_086_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_086 288 288 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 288 144 144, g32p_row24_traceSegment_086_0288_0144, g32p_row24_traceSegment_086_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_086 0 576 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 288 288, g32p_row24_traceSegment_086_0000_0288, g32p_row24_traceSegment_086_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 576 9 9, g32p_row24_traceSegment_086_0576_0009, g32p_row24_traceSegment_086_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 594 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 603 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 594 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 594 9 9, g32p_row24_traceSegment_086_0594_0009, g32p_row24_traceSegment_086_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 576 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 576 18 18, g32p_row24_traceSegment_086_0576_0018, g32p_row24_traceSegment_086_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 612 9 9, g32p_row24_traceSegment_086_0612_0009, g32p_row24_traceSegment_086_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 630 9 9, g32p_row24_traceSegment_086_0630_0009, g32p_row24_traceSegment_086_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 612 18 18, g32p_row24_traceSegment_086_0612_0018, g32p_row24_traceSegment_086_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 576 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 576 36 36, g32p_row24_traceSegment_086_0576_0036, g32p_row24_traceSegment_086_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 648 9 9, g32p_row24_traceSegment_086_0648_0009, g32p_row24_traceSegment_086_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 666 9 9, g32p_row24_traceSegment_086_0666_0009, g32p_row24_traceSegment_086_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 648 18 18, g32p_row24_traceSegment_086_0648_0018, g32p_row24_traceSegment_086_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 684 9 9, g32p_row24_traceSegment_086_0684_0009, g32p_row24_traceSegment_086_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 702 9 9, g32p_row24_traceSegment_086_0702_0009, g32p_row24_traceSegment_086_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 684 18 18, g32p_row24_traceSegment_086_0684_0018, g32p_row24_traceSegment_086_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 648 36 36, g32p_row24_traceSegment_086_0648_0036, g32p_row24_traceSegment_086_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 576 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 576 72 72, g32p_row24_traceSegment_086_0576_0072, g32p_row24_traceSegment_086_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 720 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 720 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 720 9 9, g32p_row24_traceSegment_086_0720_0009, g32p_row24_traceSegment_086_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 747 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 738 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 738 9 9, g32p_row24_traceSegment_086_0738_0009, g32p_row24_traceSegment_086_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 720 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 720 18 18, g32p_row24_traceSegment_086_0720_0018, g32p_row24_traceSegment_086_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 765 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 756 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 756 9 9, g32p_row24_traceSegment_086_0756_0009, g32p_row24_traceSegment_086_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 783 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 774 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 774 9 9, g32p_row24_traceSegment_086_0774_0009, g32p_row24_traceSegment_086_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 756 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 756 18 18, g32p_row24_traceSegment_086_0756_0018, g32p_row24_traceSegment_086_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 720 72 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 720 36 36, g32p_row24_traceSegment_086_0720_0036, g32p_row24_traceSegment_086_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 792 9 9, g32p_row24_traceSegment_086_0792_0009, g32p_row24_traceSegment_086_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 810 9 9, g32p_row24_traceSegment_086_0810_0009, g32p_row24_traceSegment_086_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 792 18 18, g32p_row24_traceSegment_086_0792_0018, g32p_row24_traceSegment_086_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 828 9 9, g32p_row24_traceSegment_086_0828_0009, g32p_row24_traceSegment_086_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 846 9 9, g32p_row24_traceSegment_086_0846_0009, g32p_row24_traceSegment_086_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 828 18 18, g32p_row24_traceSegment_086_0828_0018, g32p_row24_traceSegment_086_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 792 36 36, g32p_row24_traceSegment_086_0792_0036, g32p_row24_traceSegment_086_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 720 144 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 720 72 72, g32p_row24_traceSegment_086_0720_0072, g32p_row24_traceSegment_086_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_086 576 288 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 576 144 144, g32p_row24_traceSegment_086_0576_0144, g32p_row24_traceSegment_086_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 864 9 9, g32p_row24_traceSegment_086_0864_0009, g32p_row24_traceSegment_086_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 882 9 9, g32p_row24_traceSegment_086_0882_0009, g32p_row24_traceSegment_086_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 864 18 18, g32p_row24_traceSegment_086_0864_0018, g32p_row24_traceSegment_086_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 900 9 9, g32p_row24_traceSegment_086_0900_0009, g32p_row24_traceSegment_086_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 918 9 9, g32p_row24_traceSegment_086_0918_0009, g32p_row24_traceSegment_086_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 900 18 18, g32p_row24_traceSegment_086_0900_0018, g32p_row24_traceSegment_086_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 864 36 36, g32p_row24_traceSegment_086_0864_0036, g32p_row24_traceSegment_086_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 936 9 9, g32p_row24_traceSegment_086_0936_0009, g32p_row24_traceSegment_086_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 954 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 954 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 954 9 9, g32p_row24_traceSegment_086_0954_0009, g32p_row24_traceSegment_086_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 936 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 936 18 18, g32p_row24_traceSegment_086_0936_0018, g32p_row24_traceSegment_086_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 972 9 9, g32p_row24_traceSegment_086_0972_0009, g32p_row24_traceSegment_086_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 990 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 990 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 990 9 9, g32p_row24_traceSegment_086_0990_0009, g32p_row24_traceSegment_086_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 972 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 972 18 18, g32p_row24_traceSegment_086_0972_0018, g32p_row24_traceSegment_086_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 936 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 936 36 36, g32p_row24_traceSegment_086_0936_0036, g32p_row24_traceSegment_086_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 864 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 864 72 72, g32p_row24_traceSegment_086_0864_0072, g32p_row24_traceSegment_086_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1008 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1008 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1008 9 9, g32p_row24_traceSegment_086_1008_0009, g32p_row24_traceSegment_086_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1026 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1026 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1026 9 9, g32p_row24_traceSegment_086_1026_0009, g32p_row24_traceSegment_086_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 1008 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1008 18 18, g32p_row24_traceSegment_086_1008_0018, g32p_row24_traceSegment_086_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1044 9 9, g32p_row24_traceSegment_086_1044_0009, g32p_row24_traceSegment_086_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1062 9 9, g32p_row24_traceSegment_086_1062_0009, g32p_row24_traceSegment_086_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1044 18 18, g32p_row24_traceSegment_086_1044_0018, g32p_row24_traceSegment_086_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 1008 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1008 36 36, g32p_row24_traceSegment_086_1008_0036, g32p_row24_traceSegment_086_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1080 9 9, g32p_row24_traceSegment_086_1080_0009, g32p_row24_traceSegment_086_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1098 9 9, g32p_row24_traceSegment_086_1098_0009, g32p_row24_traceSegment_086_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1080 18 18, g32p_row24_traceSegment_086_1080_0018, g32p_row24_traceSegment_086_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1116 9 9, g32p_row24_traceSegment_086_1116_0009, g32p_row24_traceSegment_086_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_086 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_086_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_086 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1134 9 9, g32p_row24_traceSegment_086_1134_0009, g32p_row24_traceSegment_086_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_086 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1116 18 18, g32p_row24_traceSegment_086_1116_0018, g32p_row24_traceSegment_086_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_086 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1080 36 36, g32p_row24_traceSegment_086_1080_0036, g32p_row24_traceSegment_086_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_086_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_086 1008 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 1008 72 72, g32p_row24_traceSegment_086_1008_0072, g32p_row24_traceSegment_086_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_086 864 288 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 864 144 144, g32p_row24_traceSegment_086_0864_0144, g32p_row24_traceSegment_086_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_086 576 576 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 576 288 288, g32p_row24_traceSegment_086_0576_0288, g32p_row24_traceSegment_086_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_086_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_086 0 1152 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_086 0 576 576, g32p_row24_traceSegment_086_0000_0576, g32p_row24_traceSegment_086_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 86 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_086_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_090 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 90 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_090_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 9 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 0 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 9 9, g32p_row24_traceSegment_090_0000_0009, g32p_row24_traceSegment_090_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 18 9 9, g32p_row24_traceSegment_090_0018_0009, g32p_row24_traceSegment_090_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 0 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 18 18, g32p_row24_traceSegment_090_0000_0018, g32p_row24_traceSegment_090_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 36 9 9, g32p_row24_traceSegment_090_0036_0009, g32p_row24_traceSegment_090_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 54 9 9, g32p_row24_traceSegment_090_0054_0009, g32p_row24_traceSegment_090_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 36 18 18, g32p_row24_traceSegment_090_0036_0018, g32p_row24_traceSegment_090_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 0 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 36 36, g32p_row24_traceSegment_090_0000_0036, g32p_row24_traceSegment_090_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 72 9 9, g32p_row24_traceSegment_090_0072_0009, g32p_row24_traceSegment_090_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 90 9 9, g32p_row24_traceSegment_090_0090_0009, g32p_row24_traceSegment_090_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 72 18 18, g32p_row24_traceSegment_090_0072_0018, g32p_row24_traceSegment_090_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 108 9 9, g32p_row24_traceSegment_090_0108_0009, g32p_row24_traceSegment_090_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 126 9 9, g32p_row24_traceSegment_090_0126_0009, g32p_row24_traceSegment_090_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 108 18 18, g32p_row24_traceSegment_090_0108_0018, g32p_row24_traceSegment_090_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 72 36 36, g32p_row24_traceSegment_090_0072_0036, g32p_row24_traceSegment_090_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 72 72, g32p_row24_traceSegment_090_0000_0072, g32p_row24_traceSegment_090_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 144 9 9, g32p_row24_traceSegment_090_0144_0009, g32p_row24_traceSegment_090_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 171 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 162 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 162 9 9, g32p_row24_traceSegment_090_0162_0009, g32p_row24_traceSegment_090_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 144 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 144 18 18, g32p_row24_traceSegment_090_0144_0018, g32p_row24_traceSegment_090_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 180 9 9, g32p_row24_traceSegment_090_0180_0009, g32p_row24_traceSegment_090_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 198 9 9, g32p_row24_traceSegment_090_0198_0009, g32p_row24_traceSegment_090_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 180 18 18, g32p_row24_traceSegment_090_0180_0018, g32p_row24_traceSegment_090_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 144 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 144 36 36, g32p_row24_traceSegment_090_0144_0036, g32p_row24_traceSegment_090_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 216 9 9, g32p_row24_traceSegment_090_0216_0009, g32p_row24_traceSegment_090_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 234 9 9, g32p_row24_traceSegment_090_0234_0009, g32p_row24_traceSegment_090_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 216 18 18, g32p_row24_traceSegment_090_0216_0018, g32p_row24_traceSegment_090_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 261 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 252 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 252 9 9, g32p_row24_traceSegment_090_0252_0009, g32p_row24_traceSegment_090_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 270 9 9, g32p_row24_traceSegment_090_0270_0009, g32p_row24_traceSegment_090_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 252 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 252 18 18, g32p_row24_traceSegment_090_0252_0018, g32p_row24_traceSegment_090_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 216 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 216 36 36, g32p_row24_traceSegment_090_0216_0036, g32p_row24_traceSegment_090_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 144 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 144 72 72, g32p_row24_traceSegment_090_0144_0072, g32p_row24_traceSegment_090_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_090 0 288 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 144 144, g32p_row24_traceSegment_090_0000_0144, g32p_row24_traceSegment_090_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 288 9 9, g32p_row24_traceSegment_090_0288_0009, g32p_row24_traceSegment_090_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 306 9 9, g32p_row24_traceSegment_090_0306_0009, g32p_row24_traceSegment_090_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 288 18 18, g32p_row24_traceSegment_090_0288_0018, g32p_row24_traceSegment_090_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 324 9 9, g32p_row24_traceSegment_090_0324_0009, g32p_row24_traceSegment_090_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 351 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 342 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 342 9 9, g32p_row24_traceSegment_090_0342_0009, g32p_row24_traceSegment_090_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 324 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 324 18 18, g32p_row24_traceSegment_090_0324_0018, g32p_row24_traceSegment_090_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 288 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 288 36 36, g32p_row24_traceSegment_090_0288_0036, g32p_row24_traceSegment_090_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 360 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 360 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 360 9 9, g32p_row24_traceSegment_090_0360_0009, g32p_row24_traceSegment_090_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 387 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 378 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 378 9 9, g32p_row24_traceSegment_090_0378_0009, g32p_row24_traceSegment_090_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 360 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 360 18 18, g32p_row24_traceSegment_090_0360_0018, g32p_row24_traceSegment_090_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 396 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 405 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 396 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 396 9 9, g32p_row24_traceSegment_090_0396_0009, g32p_row24_traceSegment_090_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 414 9 9, g32p_row24_traceSegment_090_0414_0009, g32p_row24_traceSegment_090_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 396 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 396 18 18, g32p_row24_traceSegment_090_0396_0018, g32p_row24_traceSegment_090_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 360 72 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 360 36 36, g32p_row24_traceSegment_090_0360_0036, g32p_row24_traceSegment_090_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 288 144 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 288 72 72, g32p_row24_traceSegment_090_0288_0072, g32p_row24_traceSegment_090_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 432 9 9, g32p_row24_traceSegment_090_0432_0009, g32p_row24_traceSegment_090_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 450 9 9, g32p_row24_traceSegment_090_0450_0009, g32p_row24_traceSegment_090_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 432 18 18, g32p_row24_traceSegment_090_0432_0018, g32p_row24_traceSegment_090_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 468 9 9, g32p_row24_traceSegment_090_0468_0009, g32p_row24_traceSegment_090_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 486 9 9, g32p_row24_traceSegment_090_0486_0009, g32p_row24_traceSegment_090_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 468 18 18, g32p_row24_traceSegment_090_0468_0018, g32p_row24_traceSegment_090_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 432 36 36, g32p_row24_traceSegment_090_0432_0036, g32p_row24_traceSegment_090_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 504 9 9, g32p_row24_traceSegment_090_0504_0009, g32p_row24_traceSegment_090_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 522 9 9, g32p_row24_traceSegment_090_0522_0009, g32p_row24_traceSegment_090_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 504 18 18, g32p_row24_traceSegment_090_0504_0018, g32p_row24_traceSegment_090_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 540 9 9, g32p_row24_traceSegment_090_0540_0009, g32p_row24_traceSegment_090_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 558 9 9, g32p_row24_traceSegment_090_0558_0009, g32p_row24_traceSegment_090_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 540 18 18, g32p_row24_traceSegment_090_0540_0018, g32p_row24_traceSegment_090_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 504 36 36, g32p_row24_traceSegment_090_0504_0036, g32p_row24_traceSegment_090_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 432 72 72, g32p_row24_traceSegment_090_0432_0072, g32p_row24_traceSegment_090_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_090 288 288 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 288 144 144, g32p_row24_traceSegment_090_0288_0144, g32p_row24_traceSegment_090_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_090 0 576 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 288 288, g32p_row24_traceSegment_090_0000_0288, g32p_row24_traceSegment_090_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 576 9 9, g32p_row24_traceSegment_090_0576_0009, g32p_row24_traceSegment_090_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 594 9 9, g32p_row24_traceSegment_090_0594_0009, g32p_row24_traceSegment_090_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 576 18 18, g32p_row24_traceSegment_090_0576_0018, g32p_row24_traceSegment_090_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 612 9 9, g32p_row24_traceSegment_090_0612_0009, g32p_row24_traceSegment_090_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 630 9 9, g32p_row24_traceSegment_090_0630_0009, g32p_row24_traceSegment_090_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 612 18 18, g32p_row24_traceSegment_090_0612_0018, g32p_row24_traceSegment_090_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 576 36 36, g32p_row24_traceSegment_090_0576_0036, g32p_row24_traceSegment_090_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 648 9 9, g32p_row24_traceSegment_090_0648_0009, g32p_row24_traceSegment_090_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 666 9 9, g32p_row24_traceSegment_090_0666_0009, g32p_row24_traceSegment_090_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 648 18 18, g32p_row24_traceSegment_090_0648_0018, g32p_row24_traceSegment_090_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 684 9 9, g32p_row24_traceSegment_090_0684_0009, g32p_row24_traceSegment_090_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 702 9 9, g32p_row24_traceSegment_090_0702_0009, g32p_row24_traceSegment_090_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 684 18 18, g32p_row24_traceSegment_090_0684_0018, g32p_row24_traceSegment_090_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 648 36 36, g32p_row24_traceSegment_090_0648_0036, g32p_row24_traceSegment_090_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 576 72 72, g32p_row24_traceSegment_090_0576_0072, g32p_row24_traceSegment_090_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 720 9 9, g32p_row24_traceSegment_090_0720_0009, g32p_row24_traceSegment_090_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 738 9 9, g32p_row24_traceSegment_090_0738_0009, g32p_row24_traceSegment_090_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 720 18 18, g32p_row24_traceSegment_090_0720_0018, g32p_row24_traceSegment_090_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 756 9 9, g32p_row24_traceSegment_090_0756_0009, g32p_row24_traceSegment_090_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 774 9 9, g32p_row24_traceSegment_090_0774_0009, g32p_row24_traceSegment_090_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 756 18 18, g32p_row24_traceSegment_090_0756_0018, g32p_row24_traceSegment_090_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 720 36 36, g32p_row24_traceSegment_090_0720_0036, g32p_row24_traceSegment_090_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 792 9 9, g32p_row24_traceSegment_090_0792_0009, g32p_row24_traceSegment_090_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 810 9 9, g32p_row24_traceSegment_090_0810_0009, g32p_row24_traceSegment_090_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 792 18 18, g32p_row24_traceSegment_090_0792_0018, g32p_row24_traceSegment_090_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 828 9 9, g32p_row24_traceSegment_090_0828_0009, g32p_row24_traceSegment_090_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 846 9 9, g32p_row24_traceSegment_090_0846_0009, g32p_row24_traceSegment_090_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 828 18 18, g32p_row24_traceSegment_090_0828_0018, g32p_row24_traceSegment_090_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 792 36 36, g32p_row24_traceSegment_090_0792_0036, g32p_row24_traceSegment_090_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 720 72 72, g32p_row24_traceSegment_090_0720_0072, g32p_row24_traceSegment_090_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_090 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 576 144 144, g32p_row24_traceSegment_090_0576_0144, g32p_row24_traceSegment_090_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 864 9 9, g32p_row24_traceSegment_090_0864_0009, g32p_row24_traceSegment_090_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 882 9 9, g32p_row24_traceSegment_090_0882_0009, g32p_row24_traceSegment_090_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 864 18 18, g32p_row24_traceSegment_090_0864_0018, g32p_row24_traceSegment_090_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 900 9 9, g32p_row24_traceSegment_090_0900_0009, g32p_row24_traceSegment_090_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 918 9 9, g32p_row24_traceSegment_090_0918_0009, g32p_row24_traceSegment_090_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 900 18 18, g32p_row24_traceSegment_090_0900_0018, g32p_row24_traceSegment_090_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 864 36 36, g32p_row24_traceSegment_090_0864_0036, g32p_row24_traceSegment_090_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 936 9 9, g32p_row24_traceSegment_090_0936_0009, g32p_row24_traceSegment_090_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 954 9 9, g32p_row24_traceSegment_090_0954_0009, g32p_row24_traceSegment_090_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 936 18 18, g32p_row24_traceSegment_090_0936_0018, g32p_row24_traceSegment_090_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 972 9 9, g32p_row24_traceSegment_090_0972_0009, g32p_row24_traceSegment_090_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 990 9 9, g32p_row24_traceSegment_090_0990_0009, g32p_row24_traceSegment_090_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 972 18 18, g32p_row24_traceSegment_090_0972_0018, g32p_row24_traceSegment_090_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 936 36 36, g32p_row24_traceSegment_090_0936_0036, g32p_row24_traceSegment_090_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 864 72 72, g32p_row24_traceSegment_090_0864_0072, g32p_row24_traceSegment_090_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1008 9 9, g32p_row24_traceSegment_090_1008_0009, g32p_row24_traceSegment_090_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1026 9 9, g32p_row24_traceSegment_090_1026_0009, g32p_row24_traceSegment_090_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1008 18 18, g32p_row24_traceSegment_090_1008_0018, g32p_row24_traceSegment_090_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1044 9 9, g32p_row24_traceSegment_090_1044_0009, g32p_row24_traceSegment_090_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1062 9 9, g32p_row24_traceSegment_090_1062_0009, g32p_row24_traceSegment_090_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1044 18 18, g32p_row24_traceSegment_090_1044_0018, g32p_row24_traceSegment_090_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1008 36 36, g32p_row24_traceSegment_090_1008_0036, g32p_row24_traceSegment_090_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1080 9 9, g32p_row24_traceSegment_090_1080_0009, g32p_row24_traceSegment_090_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1098 9 9, g32p_row24_traceSegment_090_1098_0009, g32p_row24_traceSegment_090_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1080 18 18, g32p_row24_traceSegment_090_1080_0018, g32p_row24_traceSegment_090_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1116 9 9, g32p_row24_traceSegment_090_1116_0009, g32p_row24_traceSegment_090_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_090 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_090_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_090 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1134 9 9, g32p_row24_traceSegment_090_1134_0009, g32p_row24_traceSegment_090_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_090 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1116 18 18, g32p_row24_traceSegment_090_1116_0018, g32p_row24_traceSegment_090_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_090 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1080 36 36, g32p_row24_traceSegment_090_1080_0036, g32p_row24_traceSegment_090_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_090_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_090 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 1008 72 72, g32p_row24_traceSegment_090_1008_0072, g32p_row24_traceSegment_090_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_090 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 864 144 144, g32p_row24_traceSegment_090_0864_0144, g32p_row24_traceSegment_090_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_090 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 576 288 288, g32p_row24_traceSegment_090_0576_0288, g32p_row24_traceSegment_090_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_090_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_090 0 1152 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_090 0 576 576, g32p_row24_traceSegment_090_0000_0576, g32p_row24_traceSegment_090_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 90 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_090_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_094 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 94 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_094_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 9 9, g32p_row24_traceSegment_094_0000_0009, g32p_row24_traceSegment_094_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 18 9 9, g32p_row24_traceSegment_094_0018_0009, g32p_row24_traceSegment_094_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 18 18, g32p_row24_traceSegment_094_0000_0018, g32p_row24_traceSegment_094_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 36 9 9, g32p_row24_traceSegment_094_0036_0009, g32p_row24_traceSegment_094_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 63 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 54 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 54 9 9, g32p_row24_traceSegment_094_0054_0009, g32p_row24_traceSegment_094_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 36 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 36 18 18, g32p_row24_traceSegment_094_0036_0018, g32p_row24_traceSegment_094_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 0 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 36 36, g32p_row24_traceSegment_094_0000_0036, g32p_row24_traceSegment_094_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 72 9 9, g32p_row24_traceSegment_094_0072_0009, g32p_row24_traceSegment_094_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 90 9 9, g32p_row24_traceSegment_094_0090_0009, g32p_row24_traceSegment_094_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 72 18 18, g32p_row24_traceSegment_094_0072_0018, g32p_row24_traceSegment_094_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 108 9 9, g32p_row24_traceSegment_094_0108_0009, g32p_row24_traceSegment_094_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 126 9 9, g32p_row24_traceSegment_094_0126_0009, g32p_row24_traceSegment_094_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 108 18 18, g32p_row24_traceSegment_094_0108_0018, g32p_row24_traceSegment_094_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 72 36 36, g32p_row24_traceSegment_094_0072_0036, g32p_row24_traceSegment_094_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 0 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 72 72, g32p_row24_traceSegment_094_0000_0072, g32p_row24_traceSegment_094_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 144 9 9, g32p_row24_traceSegment_094_0144_0009, g32p_row24_traceSegment_094_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 162 9 9, g32p_row24_traceSegment_094_0162_0009, g32p_row24_traceSegment_094_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 144 18 18, g32p_row24_traceSegment_094_0144_0018, g32p_row24_traceSegment_094_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 180 9 9, g32p_row24_traceSegment_094_0180_0009, g32p_row24_traceSegment_094_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 198 9 9, g32p_row24_traceSegment_094_0198_0009, g32p_row24_traceSegment_094_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 180 18 18, g32p_row24_traceSegment_094_0180_0018, g32p_row24_traceSegment_094_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 144 36 36, g32p_row24_traceSegment_094_0144_0036, g32p_row24_traceSegment_094_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 216 9 9, g32p_row24_traceSegment_094_0216_0009, g32p_row24_traceSegment_094_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 234 9 9, g32p_row24_traceSegment_094_0234_0009, g32p_row24_traceSegment_094_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 216 18 18, g32p_row24_traceSegment_094_0216_0018, g32p_row24_traceSegment_094_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 252 9 9, g32p_row24_traceSegment_094_0252_0009, g32p_row24_traceSegment_094_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 270 9 9, g32p_row24_traceSegment_094_0270_0009, g32p_row24_traceSegment_094_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 252 18 18, g32p_row24_traceSegment_094_0252_0018, g32p_row24_traceSegment_094_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 216 36 36, g32p_row24_traceSegment_094_0216_0036, g32p_row24_traceSegment_094_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 144 72 72, g32p_row24_traceSegment_094_0144_0072, g32p_row24_traceSegment_094_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_094 0 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 144 144, g32p_row24_traceSegment_094_0000_0144, g32p_row24_traceSegment_094_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 288 9 9, g32p_row24_traceSegment_094_0288_0009, g32p_row24_traceSegment_094_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 306 9 9, g32p_row24_traceSegment_094_0306_0009, g32p_row24_traceSegment_094_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 288 18 18, g32p_row24_traceSegment_094_0288_0018, g32p_row24_traceSegment_094_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 324 9 9, g32p_row24_traceSegment_094_0324_0009, g32p_row24_traceSegment_094_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 342 9 9, g32p_row24_traceSegment_094_0342_0009, g32p_row24_traceSegment_094_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 324 18 18, g32p_row24_traceSegment_094_0324_0018, g32p_row24_traceSegment_094_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 288 36 36, g32p_row24_traceSegment_094_0288_0036, g32p_row24_traceSegment_094_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 360 9 9, g32p_row24_traceSegment_094_0360_0009, g32p_row24_traceSegment_094_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 378 9 9, g32p_row24_traceSegment_094_0378_0009, g32p_row24_traceSegment_094_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 360 18 18, g32p_row24_traceSegment_094_0360_0018, g32p_row24_traceSegment_094_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 396 9 9, g32p_row24_traceSegment_094_0396_0009, g32p_row24_traceSegment_094_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 414 9 9, g32p_row24_traceSegment_094_0414_0009, g32p_row24_traceSegment_094_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 396 18 18, g32p_row24_traceSegment_094_0396_0018, g32p_row24_traceSegment_094_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 360 36 36, g32p_row24_traceSegment_094_0360_0036, g32p_row24_traceSegment_094_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 288 72 72, g32p_row24_traceSegment_094_0288_0072, g32p_row24_traceSegment_094_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 432 9 9, g32p_row24_traceSegment_094_0432_0009, g32p_row24_traceSegment_094_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 450 9 9, g32p_row24_traceSegment_094_0450_0009, g32p_row24_traceSegment_094_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 432 18 18, g32p_row24_traceSegment_094_0432_0018, g32p_row24_traceSegment_094_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 468 9 9, g32p_row24_traceSegment_094_0468_0009, g32p_row24_traceSegment_094_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 486 9 9, g32p_row24_traceSegment_094_0486_0009, g32p_row24_traceSegment_094_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 468 18 18, g32p_row24_traceSegment_094_0468_0018, g32p_row24_traceSegment_094_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 432 36 36, g32p_row24_traceSegment_094_0432_0036, g32p_row24_traceSegment_094_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 513 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 504 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 504 9 9, g32p_row24_traceSegment_094_0504_0009, g32p_row24_traceSegment_094_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 522 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 522 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 522 9 9, g32p_row24_traceSegment_094_0522_0009, g32p_row24_traceSegment_094_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 504 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 504 18 18, g32p_row24_traceSegment_094_0504_0018, g32p_row24_traceSegment_094_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 540 9 9, g32p_row24_traceSegment_094_0540_0009, g32p_row24_traceSegment_094_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 558 9 9, g32p_row24_traceSegment_094_0558_0009, g32p_row24_traceSegment_094_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 540 18 18, g32p_row24_traceSegment_094_0540_0018, g32p_row24_traceSegment_094_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 504 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 504 36 36, g32p_row24_traceSegment_094_0504_0036, g32p_row24_traceSegment_094_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 432 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 432 72 72, g32p_row24_traceSegment_094_0432_0072, g32p_row24_traceSegment_094_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_094 288 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 288 144 144, g32p_row24_traceSegment_094_0288_0144, g32p_row24_traceSegment_094_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_094 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 288 288, g32p_row24_traceSegment_094_0000_0288, g32p_row24_traceSegment_094_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 576 9 9, g32p_row24_traceSegment_094_0576_0009, g32p_row24_traceSegment_094_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 594 9 9, g32p_row24_traceSegment_094_0594_0009, g32p_row24_traceSegment_094_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 576 18 18, g32p_row24_traceSegment_094_0576_0018, g32p_row24_traceSegment_094_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 612 9 9, g32p_row24_traceSegment_094_0612_0009, g32p_row24_traceSegment_094_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 630 9 9, g32p_row24_traceSegment_094_0630_0009, g32p_row24_traceSegment_094_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 612 18 18, g32p_row24_traceSegment_094_0612_0018, g32p_row24_traceSegment_094_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 576 36 36, g32p_row24_traceSegment_094_0576_0036, g32p_row24_traceSegment_094_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 648 9 9, g32p_row24_traceSegment_094_0648_0009, g32p_row24_traceSegment_094_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 666 9 9, g32p_row24_traceSegment_094_0666_0009, g32p_row24_traceSegment_094_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 648 18 18, g32p_row24_traceSegment_094_0648_0018, g32p_row24_traceSegment_094_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 684 9 9, g32p_row24_traceSegment_094_0684_0009, g32p_row24_traceSegment_094_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 702 9 9, g32p_row24_traceSegment_094_0702_0009, g32p_row24_traceSegment_094_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 684 18 18, g32p_row24_traceSegment_094_0684_0018, g32p_row24_traceSegment_094_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 648 36 36, g32p_row24_traceSegment_094_0648_0036, g32p_row24_traceSegment_094_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 576 72 72, g32p_row24_traceSegment_094_0576_0072, g32p_row24_traceSegment_094_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 720 9 9, g32p_row24_traceSegment_094_0720_0009, g32p_row24_traceSegment_094_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 738 9 9, g32p_row24_traceSegment_094_0738_0009, g32p_row24_traceSegment_094_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 720 18 18, g32p_row24_traceSegment_094_0720_0018, g32p_row24_traceSegment_094_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 756 9 9, g32p_row24_traceSegment_094_0756_0009, g32p_row24_traceSegment_094_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 774 9 9, g32p_row24_traceSegment_094_0774_0009, g32p_row24_traceSegment_094_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 756 18 18, g32p_row24_traceSegment_094_0756_0018, g32p_row24_traceSegment_094_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 720 36 36, g32p_row24_traceSegment_094_0720_0036, g32p_row24_traceSegment_094_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 792 9 9, g32p_row24_traceSegment_094_0792_0009, g32p_row24_traceSegment_094_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 819 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 810 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 810 9 9, g32p_row24_traceSegment_094_0810_0009, g32p_row24_traceSegment_094_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 792 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 792 18 18, g32p_row24_traceSegment_094_0792_0018, g32p_row24_traceSegment_094_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 828 9 9, g32p_row24_traceSegment_094_0828_0009, g32p_row24_traceSegment_094_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 855 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 846 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 846 9 9, g32p_row24_traceSegment_094_0846_0009, g32p_row24_traceSegment_094_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 828 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 828 18 18, g32p_row24_traceSegment_094_0828_0018, g32p_row24_traceSegment_094_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 792 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 792 36 36, g32p_row24_traceSegment_094_0792_0036, g32p_row24_traceSegment_094_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 720 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 720 72 72, g32p_row24_traceSegment_094_0720_0072, g32p_row24_traceSegment_094_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_094 576 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 576 144 144, g32p_row24_traceSegment_094_0576_0144, g32p_row24_traceSegment_094_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 864 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 864 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 864 9 9, g32p_row24_traceSegment_094_0864_0009, g32p_row24_traceSegment_094_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 882 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 891 9 = [3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 882 18 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 882 9 9, g32p_row24_traceSegment_094_0882_0009, g32p_row24_traceSegment_094_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 864 36 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 864 18 18, g32p_row24_traceSegment_094_0864_0018, g32p_row24_traceSegment_094_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 900 9 9, g32p_row24_traceSegment_094_0900_0009, g32p_row24_traceSegment_094_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 918 9 9, g32p_row24_traceSegment_094_0918_0009, g32p_row24_traceSegment_094_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 900 18 18, g32p_row24_traceSegment_094_0900_0018, g32p_row24_traceSegment_094_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 864 72 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 864 36 36, g32p_row24_traceSegment_094_0864_0036, g32p_row24_traceSegment_094_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 936 9 9, g32p_row24_traceSegment_094_0936_0009, g32p_row24_traceSegment_094_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 954 9 9, g32p_row24_traceSegment_094_0954_0009, g32p_row24_traceSegment_094_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 936 18 18, g32p_row24_traceSegment_094_0936_0018, g32p_row24_traceSegment_094_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 972 9 9, g32p_row24_traceSegment_094_0972_0009, g32p_row24_traceSegment_094_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 990 9 9, g32p_row24_traceSegment_094_0990_0009, g32p_row24_traceSegment_094_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 972 18 18, g32p_row24_traceSegment_094_0972_0018, g32p_row24_traceSegment_094_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 936 36 36, g32p_row24_traceSegment_094_0936_0036, g32p_row24_traceSegment_094_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 864 144 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 864 72 72, g32p_row24_traceSegment_094_0864_0072, g32p_row24_traceSegment_094_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1008 9 9, g32p_row24_traceSegment_094_1008_0009, g32p_row24_traceSegment_094_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1026 9 9, g32p_row24_traceSegment_094_1026_0009, g32p_row24_traceSegment_094_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1008 18 18, g32p_row24_traceSegment_094_1008_0018, g32p_row24_traceSegment_094_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1044 9 9, g32p_row24_traceSegment_094_1044_0009, g32p_row24_traceSegment_094_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1062 9 9, g32p_row24_traceSegment_094_1062_0009, g32p_row24_traceSegment_094_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1044 18 18, g32p_row24_traceSegment_094_1044_0018, g32p_row24_traceSegment_094_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1008 36 36, g32p_row24_traceSegment_094_1008_0036, g32p_row24_traceSegment_094_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1080 9 9, g32p_row24_traceSegment_094_1080_0009, g32p_row24_traceSegment_094_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1098 9 9, g32p_row24_traceSegment_094_1098_0009, g32p_row24_traceSegment_094_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1080 18 18, g32p_row24_traceSegment_094_1080_0018, g32p_row24_traceSegment_094_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1116 9 9, g32p_row24_traceSegment_094_1116_0009, g32p_row24_traceSegment_094_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_094 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_094_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_094 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1134 9 9, g32p_row24_traceSegment_094_1134_0009, g32p_row24_traceSegment_094_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_094 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1116 18 18, g32p_row24_traceSegment_094_1116_0018, g32p_row24_traceSegment_094_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_094 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1080 36 36, g32p_row24_traceSegment_094_1080_0036, g32p_row24_traceSegment_094_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_094_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_094 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 1008 72 72, g32p_row24_traceSegment_094_1008_0072, g32p_row24_traceSegment_094_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_094 864 288 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 864 144 144, g32p_row24_traceSegment_094_0864_0144, g32p_row24_traceSegment_094_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_094 576 576 = [8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 576 288 288, g32p_row24_traceSegment_094_0576_0288, g32p_row24_traceSegment_094_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_094_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_094 0 1152 = [12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_094 0 576 576, g32p_row24_traceSegment_094_0000_0576, g32p_row24_traceSegment_094_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 94 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_094_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_096_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 9 9, g32p_row24_traceSegment_096_0000_0009, g32p_row24_traceSegment_096_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 18 9 9, g32p_row24_traceSegment_096_0018_0009, g32p_row24_traceSegment_096_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 18 18, g32p_row24_traceSegment_096_0000_0018, g32p_row24_traceSegment_096_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 36 9 9, g32p_row24_traceSegment_096_0036_0009, g32p_row24_traceSegment_096_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 63 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 54 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 54 9 9, g32p_row24_traceSegment_096_0054_0009, g32p_row24_traceSegment_096_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 36 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 36 18 18, g32p_row24_traceSegment_096_0036_0018, g32p_row24_traceSegment_096_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 36 36, g32p_row24_traceSegment_096_0000_0036, g32p_row24_traceSegment_096_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 72 9 9, g32p_row24_traceSegment_096_0072_0009, g32p_row24_traceSegment_096_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 90 9 9, g32p_row24_traceSegment_096_0090_0009, g32p_row24_traceSegment_096_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 72 18 18, g32p_row24_traceSegment_096_0072_0018, g32p_row24_traceSegment_096_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 108 9 9, g32p_row24_traceSegment_096_0108_0009, g32p_row24_traceSegment_096_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 126 9 9, g32p_row24_traceSegment_096_0126_0009, g32p_row24_traceSegment_096_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 108 18 18, g32p_row24_traceSegment_096_0108_0018, g32p_row24_traceSegment_096_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 72 36 36, g32p_row24_traceSegment_096_0072_0036, g32p_row24_traceSegment_096_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 72 72, g32p_row24_traceSegment_096_0000_0072, g32p_row24_traceSegment_096_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 144 9 9, g32p_row24_traceSegment_096_0144_0009, g32p_row24_traceSegment_096_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 162 9 9, g32p_row24_traceSegment_096_0162_0009, g32p_row24_traceSegment_096_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 144 18 18, g32p_row24_traceSegment_096_0144_0018, g32p_row24_traceSegment_096_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 180 9 9, g32p_row24_traceSegment_096_0180_0009, g32p_row24_traceSegment_096_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 198 9 9, g32p_row24_traceSegment_096_0198_0009, g32p_row24_traceSegment_096_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 180 18 18, g32p_row24_traceSegment_096_0180_0018, g32p_row24_traceSegment_096_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 144 36 36, g32p_row24_traceSegment_096_0144_0036, g32p_row24_traceSegment_096_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 216 9 9, g32p_row24_traceSegment_096_0216_0009, g32p_row24_traceSegment_096_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 234 9 9, g32p_row24_traceSegment_096_0234_0009, g32p_row24_traceSegment_096_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 216 18 18, g32p_row24_traceSegment_096_0216_0018, g32p_row24_traceSegment_096_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 252 9 9, g32p_row24_traceSegment_096_0252_0009, g32p_row24_traceSegment_096_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 270 9 9, g32p_row24_traceSegment_096_0270_0009, g32p_row24_traceSegment_096_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 252 18 18, g32p_row24_traceSegment_096_0252_0018, g32p_row24_traceSegment_096_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 216 36 36, g32p_row24_traceSegment_096_0216_0036, g32p_row24_traceSegment_096_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 144 72 72, g32p_row24_traceSegment_096_0144_0072, g32p_row24_traceSegment_096_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_096 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 144 144, g32p_row24_traceSegment_096_0000_0144, g32p_row24_traceSegment_096_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 288 9 9, g32p_row24_traceSegment_096_0288_0009, g32p_row24_traceSegment_096_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 306 9 9, g32p_row24_traceSegment_096_0306_0009, g32p_row24_traceSegment_096_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 288 18 18, g32p_row24_traceSegment_096_0288_0018, g32p_row24_traceSegment_096_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 324 9 9, g32p_row24_traceSegment_096_0324_0009, g32p_row24_traceSegment_096_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 342 9 9, g32p_row24_traceSegment_096_0342_0009, g32p_row24_traceSegment_096_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 324 18 18, g32p_row24_traceSegment_096_0324_0018, g32p_row24_traceSegment_096_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 288 36 36, g32p_row24_traceSegment_096_0288_0036, g32p_row24_traceSegment_096_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 360 9 9, g32p_row24_traceSegment_096_0360_0009, g32p_row24_traceSegment_096_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 378 9 9, g32p_row24_traceSegment_096_0378_0009, g32p_row24_traceSegment_096_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 360 18 18, g32p_row24_traceSegment_096_0360_0018, g32p_row24_traceSegment_096_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 396 9 9, g32p_row24_traceSegment_096_0396_0009, g32p_row24_traceSegment_096_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 414 9 9, g32p_row24_traceSegment_096_0414_0009, g32p_row24_traceSegment_096_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 396 18 18, g32p_row24_traceSegment_096_0396_0018, g32p_row24_traceSegment_096_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 360 36 36, g32p_row24_traceSegment_096_0360_0036, g32p_row24_traceSegment_096_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 288 72 72, g32p_row24_traceSegment_096_0288_0072, g32p_row24_traceSegment_096_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 432 9 9, g32p_row24_traceSegment_096_0432_0009, g32p_row24_traceSegment_096_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 450 9 9, g32p_row24_traceSegment_096_0450_0009, g32p_row24_traceSegment_096_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 432 18 18, g32p_row24_traceSegment_096_0432_0018, g32p_row24_traceSegment_096_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 468 9 9, g32p_row24_traceSegment_096_0468_0009, g32p_row24_traceSegment_096_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 486 9 9, g32p_row24_traceSegment_096_0486_0009, g32p_row24_traceSegment_096_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 468 18 18, g32p_row24_traceSegment_096_0468_0018, g32p_row24_traceSegment_096_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 432 36 36, g32p_row24_traceSegment_096_0432_0036, g32p_row24_traceSegment_096_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 504 9 9, g32p_row24_traceSegment_096_0504_0009, g32p_row24_traceSegment_096_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 522 9 9, g32p_row24_traceSegment_096_0522_0009, g32p_row24_traceSegment_096_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 504 18 18, g32p_row24_traceSegment_096_0504_0018, g32p_row24_traceSegment_096_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 540 9 9, g32p_row24_traceSegment_096_0540_0009, g32p_row24_traceSegment_096_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 558 9 9, g32p_row24_traceSegment_096_0558_0009, g32p_row24_traceSegment_096_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 540 18 18, g32p_row24_traceSegment_096_0540_0018, g32p_row24_traceSegment_096_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 504 36 36, g32p_row24_traceSegment_096_0504_0036, g32p_row24_traceSegment_096_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 432 72 72, g32p_row24_traceSegment_096_0432_0072, g32p_row24_traceSegment_096_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_096 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 288 144 144, g32p_row24_traceSegment_096_0288_0144, g32p_row24_traceSegment_096_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_096 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 288 288, g32p_row24_traceSegment_096_0000_0288, g32p_row24_traceSegment_096_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 576 9 9, g32p_row24_traceSegment_096_0576_0009, g32p_row24_traceSegment_096_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 594 9 9, g32p_row24_traceSegment_096_0594_0009, g32p_row24_traceSegment_096_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 576 18 18, g32p_row24_traceSegment_096_0576_0018, g32p_row24_traceSegment_096_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 612 9 9, g32p_row24_traceSegment_096_0612_0009, g32p_row24_traceSegment_096_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 630 9 9, g32p_row24_traceSegment_096_0630_0009, g32p_row24_traceSegment_096_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 612 18 18, g32p_row24_traceSegment_096_0612_0018, g32p_row24_traceSegment_096_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 576 36 36, g32p_row24_traceSegment_096_0576_0036, g32p_row24_traceSegment_096_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 648 9 9, g32p_row24_traceSegment_096_0648_0009, g32p_row24_traceSegment_096_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 666 9 9, g32p_row24_traceSegment_096_0666_0009, g32p_row24_traceSegment_096_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 648 18 18, g32p_row24_traceSegment_096_0648_0018, g32p_row24_traceSegment_096_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 684 9 9, g32p_row24_traceSegment_096_0684_0009, g32p_row24_traceSegment_096_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 702 9 9, g32p_row24_traceSegment_096_0702_0009, g32p_row24_traceSegment_096_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 684 18 18, g32p_row24_traceSegment_096_0684_0018, g32p_row24_traceSegment_096_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 648 36 36, g32p_row24_traceSegment_096_0648_0036, g32p_row24_traceSegment_096_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 576 72 72, g32p_row24_traceSegment_096_0576_0072, g32p_row24_traceSegment_096_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 720 9 9, g32p_row24_traceSegment_096_0720_0009, g32p_row24_traceSegment_096_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 738 9 9, g32p_row24_traceSegment_096_0738_0009, g32p_row24_traceSegment_096_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 720 18 18, g32p_row24_traceSegment_096_0720_0018, g32p_row24_traceSegment_096_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 756 9 9, g32p_row24_traceSegment_096_0756_0009, g32p_row24_traceSegment_096_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 774 9 9, g32p_row24_traceSegment_096_0774_0009, g32p_row24_traceSegment_096_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 756 18 18, g32p_row24_traceSegment_096_0756_0018, g32p_row24_traceSegment_096_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 720 36 36, g32p_row24_traceSegment_096_0720_0036, g32p_row24_traceSegment_096_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 792 9 9, g32p_row24_traceSegment_096_0792_0009, g32p_row24_traceSegment_096_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 810 9 9, g32p_row24_traceSegment_096_0810_0009, g32p_row24_traceSegment_096_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 792 18 18, g32p_row24_traceSegment_096_0792_0018, g32p_row24_traceSegment_096_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 828 9 9, g32p_row24_traceSegment_096_0828_0009, g32p_row24_traceSegment_096_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 846 9 9, g32p_row24_traceSegment_096_0846_0009, g32p_row24_traceSegment_096_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 828 18 18, g32p_row24_traceSegment_096_0828_0018, g32p_row24_traceSegment_096_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 792 36 36, g32p_row24_traceSegment_096_0792_0036, g32p_row24_traceSegment_096_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 720 72 72, g32p_row24_traceSegment_096_0720_0072, g32p_row24_traceSegment_096_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_096 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 576 144 144, g32p_row24_traceSegment_096_0576_0144, g32p_row24_traceSegment_096_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 864 9 9, g32p_row24_traceSegment_096_0864_0009, g32p_row24_traceSegment_096_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 882 9 9, g32p_row24_traceSegment_096_0882_0009, g32p_row24_traceSegment_096_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 864 18 18, g32p_row24_traceSegment_096_0864_0018, g32p_row24_traceSegment_096_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 900 9 9, g32p_row24_traceSegment_096_0900_0009, g32p_row24_traceSegment_096_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 918 9 9, g32p_row24_traceSegment_096_0918_0009, g32p_row24_traceSegment_096_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 900 18 18, g32p_row24_traceSegment_096_0900_0018, g32p_row24_traceSegment_096_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 864 36 36, g32p_row24_traceSegment_096_0864_0036, g32p_row24_traceSegment_096_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 936 9 9, g32p_row24_traceSegment_096_0936_0009, g32p_row24_traceSegment_096_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 954 9 9, g32p_row24_traceSegment_096_0954_0009, g32p_row24_traceSegment_096_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 936 18 18, g32p_row24_traceSegment_096_0936_0018, g32p_row24_traceSegment_096_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 972 9 9, g32p_row24_traceSegment_096_0972_0009, g32p_row24_traceSegment_096_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 990 9 9, g32p_row24_traceSegment_096_0990_0009, g32p_row24_traceSegment_096_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 972 18 18, g32p_row24_traceSegment_096_0972_0018, g32p_row24_traceSegment_096_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 936 36 36, g32p_row24_traceSegment_096_0936_0036, g32p_row24_traceSegment_096_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 864 72 72, g32p_row24_traceSegment_096_0864_0072, g32p_row24_traceSegment_096_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1008 9 9, g32p_row24_traceSegment_096_1008_0009, g32p_row24_traceSegment_096_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1026 9 9, g32p_row24_traceSegment_096_1026_0009, g32p_row24_traceSegment_096_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1008 18 18, g32p_row24_traceSegment_096_1008_0018, g32p_row24_traceSegment_096_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1044 9 9, g32p_row24_traceSegment_096_1044_0009, g32p_row24_traceSegment_096_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1062 9 9, g32p_row24_traceSegment_096_1062_0009, g32p_row24_traceSegment_096_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1044 18 18, g32p_row24_traceSegment_096_1044_0018, g32p_row24_traceSegment_096_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1008 36 36, g32p_row24_traceSegment_096_1008_0036, g32p_row24_traceSegment_096_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1080 9 9, g32p_row24_traceSegment_096_1080_0009, g32p_row24_traceSegment_096_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1098 9 9, g32p_row24_traceSegment_096_1098_0009, g32p_row24_traceSegment_096_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1080 18 18, g32p_row24_traceSegment_096_1080_0018, g32p_row24_traceSegment_096_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1116 9 9, g32p_row24_traceSegment_096_1116_0009, g32p_row24_traceSegment_096_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_096 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_096_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_096 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1134 9 9, g32p_row24_traceSegment_096_1134_0009, g32p_row24_traceSegment_096_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_096 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1116 18 18, g32p_row24_traceSegment_096_1116_0018, g32p_row24_traceSegment_096_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_096 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1080 36 36, g32p_row24_traceSegment_096_1080_0036, g32p_row24_traceSegment_096_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_096_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_096 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 1008 72 72, g32p_row24_traceSegment_096_1008_0072, g32p_row24_traceSegment_096_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_096 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 864 144 144, g32p_row24_traceSegment_096_0864_0144, g32p_row24_traceSegment_096_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_096 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 576 288 288, g32p_row24_traceSegment_096_0576_0288, g32p_row24_traceSegment_096_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_096_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_096 0 1152 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_096 0 576 576, g32p_row24_traceSegment_096_0000_0576, g32p_row24_traceSegment_096_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_096_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_097_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 0 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 9 9, g32p_row24_traceSegment_097_0000_0009, g32p_row24_traceSegment_097_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 18 9 9, g32p_row24_traceSegment_097_0018_0009, g32p_row24_traceSegment_097_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 18 18, g32p_row24_traceSegment_097_0000_0018, g32p_row24_traceSegment_097_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 36 9 9, g32p_row24_traceSegment_097_0036_0009, g32p_row24_traceSegment_097_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 54 9 9, g32p_row24_traceSegment_097_0054_0009, g32p_row24_traceSegment_097_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 36 18 18, g32p_row24_traceSegment_097_0036_0018, g32p_row24_traceSegment_097_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 36 36, g32p_row24_traceSegment_097_0000_0036, g32p_row24_traceSegment_097_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 72 9 9, g32p_row24_traceSegment_097_0072_0009, g32p_row24_traceSegment_097_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 90 9 9, g32p_row24_traceSegment_097_0090_0009, g32p_row24_traceSegment_097_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 72 18 18, g32p_row24_traceSegment_097_0072_0018, g32p_row24_traceSegment_097_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 108 9 9, g32p_row24_traceSegment_097_0108_0009, g32p_row24_traceSegment_097_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 126 9 9, g32p_row24_traceSegment_097_0126_0009, g32p_row24_traceSegment_097_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 108 18 18, g32p_row24_traceSegment_097_0108_0018, g32p_row24_traceSegment_097_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 72 36 36, g32p_row24_traceSegment_097_0072_0036, g32p_row24_traceSegment_097_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 72 72, g32p_row24_traceSegment_097_0000_0072, g32p_row24_traceSegment_097_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 144 9 9, g32p_row24_traceSegment_097_0144_0009, g32p_row24_traceSegment_097_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 162 9 9, g32p_row24_traceSegment_097_0162_0009, g32p_row24_traceSegment_097_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 144 18 18, g32p_row24_traceSegment_097_0144_0018, g32p_row24_traceSegment_097_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 180 9 9, g32p_row24_traceSegment_097_0180_0009, g32p_row24_traceSegment_097_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 198 9 9, g32p_row24_traceSegment_097_0198_0009, g32p_row24_traceSegment_097_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 180 18 18, g32p_row24_traceSegment_097_0180_0018, g32p_row24_traceSegment_097_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 144 36 36, g32p_row24_traceSegment_097_0144_0036, g32p_row24_traceSegment_097_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 216 9 9, g32p_row24_traceSegment_097_0216_0009, g32p_row24_traceSegment_097_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 234 9 9, g32p_row24_traceSegment_097_0234_0009, g32p_row24_traceSegment_097_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 216 18 18, g32p_row24_traceSegment_097_0216_0018, g32p_row24_traceSegment_097_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 252 9 9, g32p_row24_traceSegment_097_0252_0009, g32p_row24_traceSegment_097_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 270 9 9, g32p_row24_traceSegment_097_0270_0009, g32p_row24_traceSegment_097_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 252 18 18, g32p_row24_traceSegment_097_0252_0018, g32p_row24_traceSegment_097_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 216 36 36, g32p_row24_traceSegment_097_0216_0036, g32p_row24_traceSegment_097_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 144 72 72, g32p_row24_traceSegment_097_0144_0072, g32p_row24_traceSegment_097_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_097 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 144 144, g32p_row24_traceSegment_097_0000_0144, g32p_row24_traceSegment_097_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 288 9 9, g32p_row24_traceSegment_097_0288_0009, g32p_row24_traceSegment_097_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 306 9 9, g32p_row24_traceSegment_097_0306_0009, g32p_row24_traceSegment_097_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 288 18 18, g32p_row24_traceSegment_097_0288_0018, g32p_row24_traceSegment_097_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 324 9 9, g32p_row24_traceSegment_097_0324_0009, g32p_row24_traceSegment_097_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 342 9 9, g32p_row24_traceSegment_097_0342_0009, g32p_row24_traceSegment_097_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 324 18 18, g32p_row24_traceSegment_097_0324_0018, g32p_row24_traceSegment_097_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 288 36 36, g32p_row24_traceSegment_097_0288_0036, g32p_row24_traceSegment_097_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 360 9 9, g32p_row24_traceSegment_097_0360_0009, g32p_row24_traceSegment_097_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 378 9 9, g32p_row24_traceSegment_097_0378_0009, g32p_row24_traceSegment_097_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 360 18 18, g32p_row24_traceSegment_097_0360_0018, g32p_row24_traceSegment_097_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 396 9 9, g32p_row24_traceSegment_097_0396_0009, g32p_row24_traceSegment_097_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 414 9 9, g32p_row24_traceSegment_097_0414_0009, g32p_row24_traceSegment_097_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 396 18 18, g32p_row24_traceSegment_097_0396_0018, g32p_row24_traceSegment_097_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 360 36 36, g32p_row24_traceSegment_097_0360_0036, g32p_row24_traceSegment_097_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 288 72 72, g32p_row24_traceSegment_097_0288_0072, g32p_row24_traceSegment_097_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 432 9 9, g32p_row24_traceSegment_097_0432_0009, g32p_row24_traceSegment_097_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 450 9 9, g32p_row24_traceSegment_097_0450_0009, g32p_row24_traceSegment_097_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 432 18 18, g32p_row24_traceSegment_097_0432_0018, g32p_row24_traceSegment_097_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 468 9 9, g32p_row24_traceSegment_097_0468_0009, g32p_row24_traceSegment_097_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 486 9 9, g32p_row24_traceSegment_097_0486_0009, g32p_row24_traceSegment_097_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 468 18 18, g32p_row24_traceSegment_097_0468_0018, g32p_row24_traceSegment_097_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 432 36 36, g32p_row24_traceSegment_097_0432_0036, g32p_row24_traceSegment_097_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 504 9 9, g32p_row24_traceSegment_097_0504_0009, g32p_row24_traceSegment_097_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 522 9 9, g32p_row24_traceSegment_097_0522_0009, g32p_row24_traceSegment_097_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 504 18 18, g32p_row24_traceSegment_097_0504_0018, g32p_row24_traceSegment_097_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 540 9 9, g32p_row24_traceSegment_097_0540_0009, g32p_row24_traceSegment_097_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 558 9 9, g32p_row24_traceSegment_097_0558_0009, g32p_row24_traceSegment_097_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 540 18 18, g32p_row24_traceSegment_097_0540_0018, g32p_row24_traceSegment_097_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 504 36 36, g32p_row24_traceSegment_097_0504_0036, g32p_row24_traceSegment_097_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 432 72 72, g32p_row24_traceSegment_097_0432_0072, g32p_row24_traceSegment_097_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_097 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 288 144 144, g32p_row24_traceSegment_097_0288_0144, g32p_row24_traceSegment_097_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_097 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 288 288, g32p_row24_traceSegment_097_0000_0288, g32p_row24_traceSegment_097_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 576 9 9, g32p_row24_traceSegment_097_0576_0009, g32p_row24_traceSegment_097_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 594 9 9, g32p_row24_traceSegment_097_0594_0009, g32p_row24_traceSegment_097_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 576 18 18, g32p_row24_traceSegment_097_0576_0018, g32p_row24_traceSegment_097_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 612 9 9, g32p_row24_traceSegment_097_0612_0009, g32p_row24_traceSegment_097_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 630 9 9, g32p_row24_traceSegment_097_0630_0009, g32p_row24_traceSegment_097_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 612 18 18, g32p_row24_traceSegment_097_0612_0018, g32p_row24_traceSegment_097_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 576 36 36, g32p_row24_traceSegment_097_0576_0036, g32p_row24_traceSegment_097_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 648 9 9, g32p_row24_traceSegment_097_0648_0009, g32p_row24_traceSegment_097_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 666 9 9, g32p_row24_traceSegment_097_0666_0009, g32p_row24_traceSegment_097_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 648 18 18, g32p_row24_traceSegment_097_0648_0018, g32p_row24_traceSegment_097_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 684 9 9, g32p_row24_traceSegment_097_0684_0009, g32p_row24_traceSegment_097_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 702 9 9, g32p_row24_traceSegment_097_0702_0009, g32p_row24_traceSegment_097_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 684 18 18, g32p_row24_traceSegment_097_0684_0018, g32p_row24_traceSegment_097_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 648 36 36, g32p_row24_traceSegment_097_0648_0036, g32p_row24_traceSegment_097_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 576 72 72, g32p_row24_traceSegment_097_0576_0072, g32p_row24_traceSegment_097_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 720 9 9, g32p_row24_traceSegment_097_0720_0009, g32p_row24_traceSegment_097_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 738 9 9, g32p_row24_traceSegment_097_0738_0009, g32p_row24_traceSegment_097_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 720 18 18, g32p_row24_traceSegment_097_0720_0018, g32p_row24_traceSegment_097_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 756 9 9, g32p_row24_traceSegment_097_0756_0009, g32p_row24_traceSegment_097_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 774 9 9, g32p_row24_traceSegment_097_0774_0009, g32p_row24_traceSegment_097_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 756 18 18, g32p_row24_traceSegment_097_0756_0018, g32p_row24_traceSegment_097_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 720 36 36, g32p_row24_traceSegment_097_0720_0036, g32p_row24_traceSegment_097_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 792 9 9, g32p_row24_traceSegment_097_0792_0009, g32p_row24_traceSegment_097_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 810 9 9, g32p_row24_traceSegment_097_0810_0009, g32p_row24_traceSegment_097_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 792 18 18, g32p_row24_traceSegment_097_0792_0018, g32p_row24_traceSegment_097_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 828 9 9, g32p_row24_traceSegment_097_0828_0009, g32p_row24_traceSegment_097_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 846 9 9, g32p_row24_traceSegment_097_0846_0009, g32p_row24_traceSegment_097_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 828 18 18, g32p_row24_traceSegment_097_0828_0018, g32p_row24_traceSegment_097_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 792 36 36, g32p_row24_traceSegment_097_0792_0036, g32p_row24_traceSegment_097_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 720 72 72, g32p_row24_traceSegment_097_0720_0072, g32p_row24_traceSegment_097_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_097 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 576 144 144, g32p_row24_traceSegment_097_0576_0144, g32p_row24_traceSegment_097_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 864 9 9, g32p_row24_traceSegment_097_0864_0009, g32p_row24_traceSegment_097_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 882 9 9, g32p_row24_traceSegment_097_0882_0009, g32p_row24_traceSegment_097_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 864 18 18, g32p_row24_traceSegment_097_0864_0018, g32p_row24_traceSegment_097_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 900 9 9, g32p_row24_traceSegment_097_0900_0009, g32p_row24_traceSegment_097_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 918 9 9, g32p_row24_traceSegment_097_0918_0009, g32p_row24_traceSegment_097_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 900 18 18, g32p_row24_traceSegment_097_0900_0018, g32p_row24_traceSegment_097_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 864 36 36, g32p_row24_traceSegment_097_0864_0036, g32p_row24_traceSegment_097_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 936 9 9, g32p_row24_traceSegment_097_0936_0009, g32p_row24_traceSegment_097_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 954 9 9, g32p_row24_traceSegment_097_0954_0009, g32p_row24_traceSegment_097_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 936 18 18, g32p_row24_traceSegment_097_0936_0018, g32p_row24_traceSegment_097_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 972 9 9, g32p_row24_traceSegment_097_0972_0009, g32p_row24_traceSegment_097_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 990 9 9, g32p_row24_traceSegment_097_0990_0009, g32p_row24_traceSegment_097_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 972 18 18, g32p_row24_traceSegment_097_0972_0018, g32p_row24_traceSegment_097_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 936 36 36, g32p_row24_traceSegment_097_0936_0036, g32p_row24_traceSegment_097_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 864 72 72, g32p_row24_traceSegment_097_0864_0072, g32p_row24_traceSegment_097_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1008 9 9, g32p_row24_traceSegment_097_1008_0009, g32p_row24_traceSegment_097_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1026 9 9, g32p_row24_traceSegment_097_1026_0009, g32p_row24_traceSegment_097_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1008 18 18, g32p_row24_traceSegment_097_1008_0018, g32p_row24_traceSegment_097_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1044 9 9, g32p_row24_traceSegment_097_1044_0009, g32p_row24_traceSegment_097_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1062 9 9, g32p_row24_traceSegment_097_1062_0009, g32p_row24_traceSegment_097_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1044 18 18, g32p_row24_traceSegment_097_1044_0018, g32p_row24_traceSegment_097_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1008 36 36, g32p_row24_traceSegment_097_1008_0036, g32p_row24_traceSegment_097_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1080 9 9, g32p_row24_traceSegment_097_1080_0009, g32p_row24_traceSegment_097_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1098 9 9, g32p_row24_traceSegment_097_1098_0009, g32p_row24_traceSegment_097_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1080 18 18, g32p_row24_traceSegment_097_1080_0018, g32p_row24_traceSegment_097_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1116 9 9, g32p_row24_traceSegment_097_1116_0009, g32p_row24_traceSegment_097_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_097 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_097_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_097 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1134 9 9, g32p_row24_traceSegment_097_1134_0009, g32p_row24_traceSegment_097_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_097 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1116 18 18, g32p_row24_traceSegment_097_1116_0018, g32p_row24_traceSegment_097_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_097 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1080 36 36, g32p_row24_traceSegment_097_1080_0036, g32p_row24_traceSegment_097_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_097_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_097 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 1008 72 72, g32p_row24_traceSegment_097_1008_0072, g32p_row24_traceSegment_097_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_097 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 864 144 144, g32p_row24_traceSegment_097_0864_0144, g32p_row24_traceSegment_097_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_097 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 576 288 288, g32p_row24_traceSegment_097_0576_0288, g32p_row24_traceSegment_097_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_097_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_097 0 1152 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_097 0 576 576, g32p_row24_traceSegment_097_0000_0576, g32p_row24_traceSegment_097_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_097_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_099_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 9 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 9 9, g32p_row24_traceSegment_099_0000_0009, g32p_row24_traceSegment_099_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 18 9 9, g32p_row24_traceSegment_099_0018_0009, g32p_row24_traceSegment_099_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 18 18, g32p_row24_traceSegment_099_0000_0018, g32p_row24_traceSegment_099_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 36 9 9, g32p_row24_traceSegment_099_0036_0009, g32p_row24_traceSegment_099_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 54 9 9, g32p_row24_traceSegment_099_0054_0009, g32p_row24_traceSegment_099_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 36 18 18, g32p_row24_traceSegment_099_0036_0018, g32p_row24_traceSegment_099_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 36 36, g32p_row24_traceSegment_099_0000_0036, g32p_row24_traceSegment_099_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 72 9 9, g32p_row24_traceSegment_099_0072_0009, g32p_row24_traceSegment_099_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 90 9 9, g32p_row24_traceSegment_099_0090_0009, g32p_row24_traceSegment_099_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 72 18 18, g32p_row24_traceSegment_099_0072_0018, g32p_row24_traceSegment_099_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 108 9 9, g32p_row24_traceSegment_099_0108_0009, g32p_row24_traceSegment_099_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 126 9 9, g32p_row24_traceSegment_099_0126_0009, g32p_row24_traceSegment_099_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 108 18 18, g32p_row24_traceSegment_099_0108_0018, g32p_row24_traceSegment_099_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 72 36 36, g32p_row24_traceSegment_099_0072_0036, g32p_row24_traceSegment_099_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 72 72, g32p_row24_traceSegment_099_0000_0072, g32p_row24_traceSegment_099_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 144 9 9, g32p_row24_traceSegment_099_0144_0009, g32p_row24_traceSegment_099_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 162 9 9, g32p_row24_traceSegment_099_0162_0009, g32p_row24_traceSegment_099_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 144 18 18, g32p_row24_traceSegment_099_0144_0018, g32p_row24_traceSegment_099_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 180 9 9, g32p_row24_traceSegment_099_0180_0009, g32p_row24_traceSegment_099_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 198 9 9, g32p_row24_traceSegment_099_0198_0009, g32p_row24_traceSegment_099_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 180 18 18, g32p_row24_traceSegment_099_0180_0018, g32p_row24_traceSegment_099_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 144 36 36, g32p_row24_traceSegment_099_0144_0036, g32p_row24_traceSegment_099_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 216 9 9, g32p_row24_traceSegment_099_0216_0009, g32p_row24_traceSegment_099_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 234 9 9, g32p_row24_traceSegment_099_0234_0009, g32p_row24_traceSegment_099_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 216 18 18, g32p_row24_traceSegment_099_0216_0018, g32p_row24_traceSegment_099_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 252 9 9, g32p_row24_traceSegment_099_0252_0009, g32p_row24_traceSegment_099_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 270 9 9, g32p_row24_traceSegment_099_0270_0009, g32p_row24_traceSegment_099_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 252 18 18, g32p_row24_traceSegment_099_0252_0018, g32p_row24_traceSegment_099_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 216 36 36, g32p_row24_traceSegment_099_0216_0036, g32p_row24_traceSegment_099_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 144 72 72, g32p_row24_traceSegment_099_0144_0072, g32p_row24_traceSegment_099_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_099 0 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 144 144, g32p_row24_traceSegment_099_0000_0144, g32p_row24_traceSegment_099_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 288 9 9, g32p_row24_traceSegment_099_0288_0009, g32p_row24_traceSegment_099_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 306 9 9, g32p_row24_traceSegment_099_0306_0009, g32p_row24_traceSegment_099_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 288 18 18, g32p_row24_traceSegment_099_0288_0018, g32p_row24_traceSegment_099_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 324 9 9, g32p_row24_traceSegment_099_0324_0009, g32p_row24_traceSegment_099_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 342 9 9, g32p_row24_traceSegment_099_0342_0009, g32p_row24_traceSegment_099_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 324 18 18, g32p_row24_traceSegment_099_0324_0018, g32p_row24_traceSegment_099_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 288 36 36, g32p_row24_traceSegment_099_0288_0036, g32p_row24_traceSegment_099_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 360 9 9, g32p_row24_traceSegment_099_0360_0009, g32p_row24_traceSegment_099_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 378 9 9, g32p_row24_traceSegment_099_0378_0009, g32p_row24_traceSegment_099_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 360 18 18, g32p_row24_traceSegment_099_0360_0018, g32p_row24_traceSegment_099_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 396 9 9, g32p_row24_traceSegment_099_0396_0009, g32p_row24_traceSegment_099_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 414 9 9, g32p_row24_traceSegment_099_0414_0009, g32p_row24_traceSegment_099_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 396 18 18, g32p_row24_traceSegment_099_0396_0018, g32p_row24_traceSegment_099_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 360 36 36, g32p_row24_traceSegment_099_0360_0036, g32p_row24_traceSegment_099_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 288 72 72, g32p_row24_traceSegment_099_0288_0072, g32p_row24_traceSegment_099_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 432 9 9, g32p_row24_traceSegment_099_0432_0009, g32p_row24_traceSegment_099_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 450 9 9, g32p_row24_traceSegment_099_0450_0009, g32p_row24_traceSegment_099_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 432 18 18, g32p_row24_traceSegment_099_0432_0018, g32p_row24_traceSegment_099_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 468 9 9, g32p_row24_traceSegment_099_0468_0009, g32p_row24_traceSegment_099_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 486 9 9, g32p_row24_traceSegment_099_0486_0009, g32p_row24_traceSegment_099_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 468 18 18, g32p_row24_traceSegment_099_0468_0018, g32p_row24_traceSegment_099_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 432 36 36, g32p_row24_traceSegment_099_0432_0036, g32p_row24_traceSegment_099_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 504 9 9, g32p_row24_traceSegment_099_0504_0009, g32p_row24_traceSegment_099_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 522 9 9, g32p_row24_traceSegment_099_0522_0009, g32p_row24_traceSegment_099_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 504 18 18, g32p_row24_traceSegment_099_0504_0018, g32p_row24_traceSegment_099_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 540 9 9, g32p_row24_traceSegment_099_0540_0009, g32p_row24_traceSegment_099_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 558 9 9, g32p_row24_traceSegment_099_0558_0009, g32p_row24_traceSegment_099_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 540 18 18, g32p_row24_traceSegment_099_0540_0018, g32p_row24_traceSegment_099_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 504 36 36, g32p_row24_traceSegment_099_0504_0036, g32p_row24_traceSegment_099_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 432 72 72, g32p_row24_traceSegment_099_0432_0072, g32p_row24_traceSegment_099_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_099 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 288 144 144, g32p_row24_traceSegment_099_0288_0144, g32p_row24_traceSegment_099_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_099 0 576 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 288 288, g32p_row24_traceSegment_099_0000_0288, g32p_row24_traceSegment_099_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 576 9 9, g32p_row24_traceSegment_099_0576_0009, g32p_row24_traceSegment_099_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 594 9 9, g32p_row24_traceSegment_099_0594_0009, g32p_row24_traceSegment_099_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 576 18 18, g32p_row24_traceSegment_099_0576_0018, g32p_row24_traceSegment_099_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 612 9 9, g32p_row24_traceSegment_099_0612_0009, g32p_row24_traceSegment_099_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 630 9 9, g32p_row24_traceSegment_099_0630_0009, g32p_row24_traceSegment_099_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 612 18 18, g32p_row24_traceSegment_099_0612_0018, g32p_row24_traceSegment_099_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 576 36 36, g32p_row24_traceSegment_099_0576_0036, g32p_row24_traceSegment_099_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 648 9 9, g32p_row24_traceSegment_099_0648_0009, g32p_row24_traceSegment_099_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 666 9 9, g32p_row24_traceSegment_099_0666_0009, g32p_row24_traceSegment_099_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 648 18 18, g32p_row24_traceSegment_099_0648_0018, g32p_row24_traceSegment_099_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 684 9 9, g32p_row24_traceSegment_099_0684_0009, g32p_row24_traceSegment_099_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 702 9 9, g32p_row24_traceSegment_099_0702_0009, g32p_row24_traceSegment_099_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 684 18 18, g32p_row24_traceSegment_099_0684_0018, g32p_row24_traceSegment_099_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 648 36 36, g32p_row24_traceSegment_099_0648_0036, g32p_row24_traceSegment_099_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 576 72 72, g32p_row24_traceSegment_099_0576_0072, g32p_row24_traceSegment_099_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 720 9 9, g32p_row24_traceSegment_099_0720_0009, g32p_row24_traceSegment_099_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 738 9 9, g32p_row24_traceSegment_099_0738_0009, g32p_row24_traceSegment_099_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 720 18 18, g32p_row24_traceSegment_099_0720_0018, g32p_row24_traceSegment_099_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 756 9 9, g32p_row24_traceSegment_099_0756_0009, g32p_row24_traceSegment_099_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 774 9 9, g32p_row24_traceSegment_099_0774_0009, g32p_row24_traceSegment_099_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 756 18 18, g32p_row24_traceSegment_099_0756_0018, g32p_row24_traceSegment_099_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 720 36 36, g32p_row24_traceSegment_099_0720_0036, g32p_row24_traceSegment_099_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 792 9 9, g32p_row24_traceSegment_099_0792_0009, g32p_row24_traceSegment_099_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 810 9 9, g32p_row24_traceSegment_099_0810_0009, g32p_row24_traceSegment_099_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 792 18 18, g32p_row24_traceSegment_099_0792_0018, g32p_row24_traceSegment_099_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 828 9 9, g32p_row24_traceSegment_099_0828_0009, g32p_row24_traceSegment_099_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 846 9 9, g32p_row24_traceSegment_099_0846_0009, g32p_row24_traceSegment_099_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 828 18 18, g32p_row24_traceSegment_099_0828_0018, g32p_row24_traceSegment_099_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 792 36 36, g32p_row24_traceSegment_099_0792_0036, g32p_row24_traceSegment_099_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 720 72 72, g32p_row24_traceSegment_099_0720_0072, g32p_row24_traceSegment_099_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_099 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 576 144 144, g32p_row24_traceSegment_099_0576_0144, g32p_row24_traceSegment_099_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 864 9 9, g32p_row24_traceSegment_099_0864_0009, g32p_row24_traceSegment_099_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 882 9 9, g32p_row24_traceSegment_099_0882_0009, g32p_row24_traceSegment_099_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 864 18 18, g32p_row24_traceSegment_099_0864_0018, g32p_row24_traceSegment_099_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 900 9 9, g32p_row24_traceSegment_099_0900_0009, g32p_row24_traceSegment_099_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 918 9 9, g32p_row24_traceSegment_099_0918_0009, g32p_row24_traceSegment_099_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 900 18 18, g32p_row24_traceSegment_099_0900_0018, g32p_row24_traceSegment_099_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 864 36 36, g32p_row24_traceSegment_099_0864_0036, g32p_row24_traceSegment_099_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 936 9 9, g32p_row24_traceSegment_099_0936_0009, g32p_row24_traceSegment_099_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 954 9 9, g32p_row24_traceSegment_099_0954_0009, g32p_row24_traceSegment_099_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 936 18 18, g32p_row24_traceSegment_099_0936_0018, g32p_row24_traceSegment_099_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 972 9 9, g32p_row24_traceSegment_099_0972_0009, g32p_row24_traceSegment_099_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 990 9 9, g32p_row24_traceSegment_099_0990_0009, g32p_row24_traceSegment_099_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 972 18 18, g32p_row24_traceSegment_099_0972_0018, g32p_row24_traceSegment_099_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 936 36 36, g32p_row24_traceSegment_099_0936_0036, g32p_row24_traceSegment_099_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 864 72 72, g32p_row24_traceSegment_099_0864_0072, g32p_row24_traceSegment_099_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1008 9 9, g32p_row24_traceSegment_099_1008_0009, g32p_row24_traceSegment_099_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1026 9 9, g32p_row24_traceSegment_099_1026_0009, g32p_row24_traceSegment_099_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1008 18 18, g32p_row24_traceSegment_099_1008_0018, g32p_row24_traceSegment_099_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1044 9 9, g32p_row24_traceSegment_099_1044_0009, g32p_row24_traceSegment_099_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1062 9 9, g32p_row24_traceSegment_099_1062_0009, g32p_row24_traceSegment_099_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1044 18 18, g32p_row24_traceSegment_099_1044_0018, g32p_row24_traceSegment_099_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1008 36 36, g32p_row24_traceSegment_099_1008_0036, g32p_row24_traceSegment_099_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1080 9 9, g32p_row24_traceSegment_099_1080_0009, g32p_row24_traceSegment_099_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1098 9 9, g32p_row24_traceSegment_099_1098_0009, g32p_row24_traceSegment_099_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1080 18 18, g32p_row24_traceSegment_099_1080_0018, g32p_row24_traceSegment_099_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1116 9 9, g32p_row24_traceSegment_099_1116_0009, g32p_row24_traceSegment_099_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_099 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_099_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_099 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1134 9 9, g32p_row24_traceSegment_099_1134_0009, g32p_row24_traceSegment_099_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_099 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1116 18 18, g32p_row24_traceSegment_099_1116_0018, g32p_row24_traceSegment_099_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_099 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1080 36 36, g32p_row24_traceSegment_099_1080_0036, g32p_row24_traceSegment_099_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_099_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_099 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 1008 72 72, g32p_row24_traceSegment_099_1008_0072, g32p_row24_traceSegment_099_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_099 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 864 144 144, g32p_row24_traceSegment_099_0864_0144, g32p_row24_traceSegment_099_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_099 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 576 288 288, g32p_row24_traceSegment_099_0576_0288, g32p_row24_traceSegment_099_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_099_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_099 0 1152 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_099 0 576 576, g32p_row24_traceSegment_099_0000_0576, g32p_row24_traceSegment_099_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_099_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row24_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 83) (g32p_literalTraceValue 23 83)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_083]
  decide +kernel

theorem g32p_row24_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 84) (g32p_literalTraceValue 23 84)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_084]
  decide +kernel

theorem g32p_row24_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 86) (g32p_literalTraceValue 23 86)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_086]
  decide +kernel

theorem g32p_row24_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 90) (g32p_literalTraceValue 23 90)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row24_traceCoefficients_090]
  decide +kernel

theorem g32p_row24_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 94) (g32p_literalTraceValue 23 94)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_094]
  decide +kernel

theorem g32p_row24_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 96) (g32p_literalTraceValue 23 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_096]
  decide +kernel

theorem g32p_row24_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 97) (g32p_literalTraceValue 23 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_097]
  decide +kernel

theorem g32p_row24_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 99) (g32p_literalTraceValue 23 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row24_traceCoefficients_099]
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

private def g32p_row24_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_101_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 9 9, g32p_row24_traceSegment_101_0000_0009, g32p_row24_traceSegment_101_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 18 9 9, g32p_row24_traceSegment_101_0018_0009, g32p_row24_traceSegment_101_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 18 18, g32p_row24_traceSegment_101_0000_0018, g32p_row24_traceSegment_101_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 36 9 9, g32p_row24_traceSegment_101_0036_0009, g32p_row24_traceSegment_101_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 63 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 54 9 9, g32p_row24_traceSegment_101_0054_0009, g32p_row24_traceSegment_101_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 36 18 18, g32p_row24_traceSegment_101_0036_0018, g32p_row24_traceSegment_101_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 0 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 36 36, g32p_row24_traceSegment_101_0000_0036, g32p_row24_traceSegment_101_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 72 9 9, g32p_row24_traceSegment_101_0072_0009, g32p_row24_traceSegment_101_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 90 9 9, g32p_row24_traceSegment_101_0090_0009, g32p_row24_traceSegment_101_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 72 18 18, g32p_row24_traceSegment_101_0072_0018, g32p_row24_traceSegment_101_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 108 9 9, g32p_row24_traceSegment_101_0108_0009, g32p_row24_traceSegment_101_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 126 9 9, g32p_row24_traceSegment_101_0126_0009, g32p_row24_traceSegment_101_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 108 18 18, g32p_row24_traceSegment_101_0108_0018, g32p_row24_traceSegment_101_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 72 36 36, g32p_row24_traceSegment_101_0072_0036, g32p_row24_traceSegment_101_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 72 72, g32p_row24_traceSegment_101_0000_0072, g32p_row24_traceSegment_101_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 144 9 9, g32p_row24_traceSegment_101_0144_0009, g32p_row24_traceSegment_101_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 162 9 9, g32p_row24_traceSegment_101_0162_0009, g32p_row24_traceSegment_101_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 144 18 18, g32p_row24_traceSegment_101_0144_0018, g32p_row24_traceSegment_101_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 180 9 9, g32p_row24_traceSegment_101_0180_0009, g32p_row24_traceSegment_101_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 198 9 9, g32p_row24_traceSegment_101_0198_0009, g32p_row24_traceSegment_101_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 180 18 18, g32p_row24_traceSegment_101_0180_0018, g32p_row24_traceSegment_101_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 144 36 36, g32p_row24_traceSegment_101_0144_0036, g32p_row24_traceSegment_101_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 216 9 9, g32p_row24_traceSegment_101_0216_0009, g32p_row24_traceSegment_101_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 234 9 9, g32p_row24_traceSegment_101_0234_0009, g32p_row24_traceSegment_101_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 216 18 18, g32p_row24_traceSegment_101_0216_0018, g32p_row24_traceSegment_101_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 252 9 9, g32p_row24_traceSegment_101_0252_0009, g32p_row24_traceSegment_101_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 270 9 9, g32p_row24_traceSegment_101_0270_0009, g32p_row24_traceSegment_101_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 252 18 18, g32p_row24_traceSegment_101_0252_0018, g32p_row24_traceSegment_101_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 216 36 36, g32p_row24_traceSegment_101_0216_0036, g32p_row24_traceSegment_101_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 144 72 72, g32p_row24_traceSegment_101_0144_0072, g32p_row24_traceSegment_101_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_101 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 144 144, g32p_row24_traceSegment_101_0000_0144, g32p_row24_traceSegment_101_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 288 9 9, g32p_row24_traceSegment_101_0288_0009, g32p_row24_traceSegment_101_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 306 9 9, g32p_row24_traceSegment_101_0306_0009, g32p_row24_traceSegment_101_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 288 18 18, g32p_row24_traceSegment_101_0288_0018, g32p_row24_traceSegment_101_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 324 9 9, g32p_row24_traceSegment_101_0324_0009, g32p_row24_traceSegment_101_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 342 9 9, g32p_row24_traceSegment_101_0342_0009, g32p_row24_traceSegment_101_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 324 18 18, g32p_row24_traceSegment_101_0324_0018, g32p_row24_traceSegment_101_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 288 36 36, g32p_row24_traceSegment_101_0288_0036, g32p_row24_traceSegment_101_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 360 9 9, g32p_row24_traceSegment_101_0360_0009, g32p_row24_traceSegment_101_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 378 9 9, g32p_row24_traceSegment_101_0378_0009, g32p_row24_traceSegment_101_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 360 18 18, g32p_row24_traceSegment_101_0360_0018, g32p_row24_traceSegment_101_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 396 9 9, g32p_row24_traceSegment_101_0396_0009, g32p_row24_traceSegment_101_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 414 9 9, g32p_row24_traceSegment_101_0414_0009, g32p_row24_traceSegment_101_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 396 18 18, g32p_row24_traceSegment_101_0396_0018, g32p_row24_traceSegment_101_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 360 36 36, g32p_row24_traceSegment_101_0360_0036, g32p_row24_traceSegment_101_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 288 72 72, g32p_row24_traceSegment_101_0288_0072, g32p_row24_traceSegment_101_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 432 9 9, g32p_row24_traceSegment_101_0432_0009, g32p_row24_traceSegment_101_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 450 9 9, g32p_row24_traceSegment_101_0450_0009, g32p_row24_traceSegment_101_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 432 18 18, g32p_row24_traceSegment_101_0432_0018, g32p_row24_traceSegment_101_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 468 9 9, g32p_row24_traceSegment_101_0468_0009, g32p_row24_traceSegment_101_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 486 9 9, g32p_row24_traceSegment_101_0486_0009, g32p_row24_traceSegment_101_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 468 18 18, g32p_row24_traceSegment_101_0468_0018, g32p_row24_traceSegment_101_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 432 36 36, g32p_row24_traceSegment_101_0432_0036, g32p_row24_traceSegment_101_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 504 9 9, g32p_row24_traceSegment_101_0504_0009, g32p_row24_traceSegment_101_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 522 9 9, g32p_row24_traceSegment_101_0522_0009, g32p_row24_traceSegment_101_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 504 18 18, g32p_row24_traceSegment_101_0504_0018, g32p_row24_traceSegment_101_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 540 9 9, g32p_row24_traceSegment_101_0540_0009, g32p_row24_traceSegment_101_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 558 9 9, g32p_row24_traceSegment_101_0558_0009, g32p_row24_traceSegment_101_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 540 18 18, g32p_row24_traceSegment_101_0540_0018, g32p_row24_traceSegment_101_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 504 36 36, g32p_row24_traceSegment_101_0504_0036, g32p_row24_traceSegment_101_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 432 72 72, g32p_row24_traceSegment_101_0432_0072, g32p_row24_traceSegment_101_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_101 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 288 144 144, g32p_row24_traceSegment_101_0288_0144, g32p_row24_traceSegment_101_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_101 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 288 288, g32p_row24_traceSegment_101_0000_0288, g32p_row24_traceSegment_101_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 576 9 9, g32p_row24_traceSegment_101_0576_0009, g32p_row24_traceSegment_101_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 594 9 9, g32p_row24_traceSegment_101_0594_0009, g32p_row24_traceSegment_101_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 576 18 18, g32p_row24_traceSegment_101_0576_0018, g32p_row24_traceSegment_101_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 612 9 9, g32p_row24_traceSegment_101_0612_0009, g32p_row24_traceSegment_101_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 630 9 9, g32p_row24_traceSegment_101_0630_0009, g32p_row24_traceSegment_101_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 612 18 18, g32p_row24_traceSegment_101_0612_0018, g32p_row24_traceSegment_101_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 576 36 36, g32p_row24_traceSegment_101_0576_0036, g32p_row24_traceSegment_101_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 648 9 9, g32p_row24_traceSegment_101_0648_0009, g32p_row24_traceSegment_101_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 666 9 9, g32p_row24_traceSegment_101_0666_0009, g32p_row24_traceSegment_101_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 648 18 18, g32p_row24_traceSegment_101_0648_0018, g32p_row24_traceSegment_101_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 684 9 9, g32p_row24_traceSegment_101_0684_0009, g32p_row24_traceSegment_101_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 702 9 9, g32p_row24_traceSegment_101_0702_0009, g32p_row24_traceSegment_101_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 684 18 18, g32p_row24_traceSegment_101_0684_0018, g32p_row24_traceSegment_101_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 648 36 36, g32p_row24_traceSegment_101_0648_0036, g32p_row24_traceSegment_101_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 576 72 72, g32p_row24_traceSegment_101_0576_0072, g32p_row24_traceSegment_101_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 720 9 9, g32p_row24_traceSegment_101_0720_0009, g32p_row24_traceSegment_101_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 738 9 9, g32p_row24_traceSegment_101_0738_0009, g32p_row24_traceSegment_101_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 720 18 18, g32p_row24_traceSegment_101_0720_0018, g32p_row24_traceSegment_101_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 756 9 9, g32p_row24_traceSegment_101_0756_0009, g32p_row24_traceSegment_101_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 774 9 9, g32p_row24_traceSegment_101_0774_0009, g32p_row24_traceSegment_101_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 756 18 18, g32p_row24_traceSegment_101_0756_0018, g32p_row24_traceSegment_101_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 720 36 36, g32p_row24_traceSegment_101_0720_0036, g32p_row24_traceSegment_101_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 792 9 9, g32p_row24_traceSegment_101_0792_0009, g32p_row24_traceSegment_101_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 810 9 9, g32p_row24_traceSegment_101_0810_0009, g32p_row24_traceSegment_101_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 792 18 18, g32p_row24_traceSegment_101_0792_0018, g32p_row24_traceSegment_101_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 828 9 9, g32p_row24_traceSegment_101_0828_0009, g32p_row24_traceSegment_101_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 846 9 9, g32p_row24_traceSegment_101_0846_0009, g32p_row24_traceSegment_101_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 828 18 18, g32p_row24_traceSegment_101_0828_0018, g32p_row24_traceSegment_101_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 792 36 36, g32p_row24_traceSegment_101_0792_0036, g32p_row24_traceSegment_101_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 720 72 72, g32p_row24_traceSegment_101_0720_0072, g32p_row24_traceSegment_101_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_101 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 576 144 144, g32p_row24_traceSegment_101_0576_0144, g32p_row24_traceSegment_101_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 864 9 9, g32p_row24_traceSegment_101_0864_0009, g32p_row24_traceSegment_101_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 882 9 9, g32p_row24_traceSegment_101_0882_0009, g32p_row24_traceSegment_101_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 864 18 18, g32p_row24_traceSegment_101_0864_0018, g32p_row24_traceSegment_101_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 900 9 9, g32p_row24_traceSegment_101_0900_0009, g32p_row24_traceSegment_101_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 918 9 9, g32p_row24_traceSegment_101_0918_0009, g32p_row24_traceSegment_101_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 900 18 18, g32p_row24_traceSegment_101_0900_0018, g32p_row24_traceSegment_101_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 864 36 36, g32p_row24_traceSegment_101_0864_0036, g32p_row24_traceSegment_101_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 936 9 9, g32p_row24_traceSegment_101_0936_0009, g32p_row24_traceSegment_101_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 954 9 9, g32p_row24_traceSegment_101_0954_0009, g32p_row24_traceSegment_101_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 936 18 18, g32p_row24_traceSegment_101_0936_0018, g32p_row24_traceSegment_101_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 972 9 9, g32p_row24_traceSegment_101_0972_0009, g32p_row24_traceSegment_101_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 990 9 9, g32p_row24_traceSegment_101_0990_0009, g32p_row24_traceSegment_101_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 972 18 18, g32p_row24_traceSegment_101_0972_0018, g32p_row24_traceSegment_101_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 936 36 36, g32p_row24_traceSegment_101_0936_0036, g32p_row24_traceSegment_101_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 864 72 72, g32p_row24_traceSegment_101_0864_0072, g32p_row24_traceSegment_101_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1008 9 9, g32p_row24_traceSegment_101_1008_0009, g32p_row24_traceSegment_101_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1026 9 9, g32p_row24_traceSegment_101_1026_0009, g32p_row24_traceSegment_101_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1008 18 18, g32p_row24_traceSegment_101_1008_0018, g32p_row24_traceSegment_101_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1044 9 9, g32p_row24_traceSegment_101_1044_0009, g32p_row24_traceSegment_101_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1062 9 9, g32p_row24_traceSegment_101_1062_0009, g32p_row24_traceSegment_101_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1044 18 18, g32p_row24_traceSegment_101_1044_0018, g32p_row24_traceSegment_101_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1008 36 36, g32p_row24_traceSegment_101_1008_0036, g32p_row24_traceSegment_101_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1080 9 9, g32p_row24_traceSegment_101_1080_0009, g32p_row24_traceSegment_101_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1098 9 9, g32p_row24_traceSegment_101_1098_0009, g32p_row24_traceSegment_101_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1080 18 18, g32p_row24_traceSegment_101_1080_0018, g32p_row24_traceSegment_101_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1116 9 9, g32p_row24_traceSegment_101_1116_0009, g32p_row24_traceSegment_101_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_101 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_101_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_101 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1134 9 9, g32p_row24_traceSegment_101_1134_0009, g32p_row24_traceSegment_101_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_101 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1116 18 18, g32p_row24_traceSegment_101_1116_0018, g32p_row24_traceSegment_101_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_101 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1080 36 36, g32p_row24_traceSegment_101_1080_0036, g32p_row24_traceSegment_101_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_101_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_101 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 1008 72 72, g32p_row24_traceSegment_101_1008_0072, g32p_row24_traceSegment_101_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_101 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 864 144 144, g32p_row24_traceSegment_101_0864_0144, g32p_row24_traceSegment_101_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_101 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 576 288 288, g32p_row24_traceSegment_101_0576_0288, g32p_row24_traceSegment_101_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_101_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_101 0 1152 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_101 0 576 576, g32p_row24_traceSegment_101_0000_0576, g32p_row24_traceSegment_101_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_101_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row24_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 101) (g32p_literalTraceValue 23 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row24_traceCoefficients_101]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row24_generatorIndex : Fin 8 → Fin 408 :=
  ![23, 74, 125, 176, 250, 251, 352, 353]

theorem g32p_row24_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup19_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 23 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 23 g32p_row24_supplierClass
    g32p_row24_supplierClass_isConj g32p_supplierGroup19_support g32p_row24_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row24_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup19_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row24_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 23 c false (g32p_row24_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 23 c true (g32p_row24_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 23 c false (g32p_row24_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 23 c true (g32p_row24_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 23 c false (g32p_row24_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 23 c false (g32p_row24_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 23 c true (g32p_row24_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 23 c true (g32p_row24_coinduced_zero c hc true) 3

theorem g32p_row24_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup19_support →
      g32p_literalTraceValue (g32p_row24_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row24_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup19_support) :
    g32p_literalTraceValue (g32p_row24_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup19_support →
    g32p_literalTraceValue (g32p_row24_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row24_zeroTrace_block_00 r k
  · exact g32p_row24_zeroTrace_block_01 r k
  · exact g32p_row24_zeroTrace_block_02 r k
  · exact g32p_row24_zeroTrace_block_03 r k
  · exact g32p_row24_zeroTrace_block_04 r k
  · exact g32p_row24_zeroTrace_block_05 r k
  · exact g32p_row24_zeroTrace_block_06 r k

theorem g32p_row24_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup19_support) :
    (g32p_recordedInductionGenerators (g32p_row24_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row24_generatorIndex k) c) := by
  rw [g32p_row24_recordedGenerator_zero c hc k, g32p_row24_zeroTrace_arithmetic c k hc]
  norm_num [HurwitzPrymRex_ev]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row24_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 6912, 6912] else [])) else (if i.val < 16 then [3456, 3456, 3456] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [41472, 41472] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [3456, 3456, 3456] else (if i.val < 33 then [10368, 10368, 10368] else [])) else (if i.val < 36 then (if i.val < 35 then [3456, 10368, 10368] else [10368, 10368, 10368]) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [3456, 3456] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 3456, 3456] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [-3456] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [-38016, 3456, 3456])) else (if i.val < 67 then [3456, 3456, 3456] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [6912, 6912] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 41472, 41472] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [3456, 3456, 3456] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row24_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup19_support) :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) c) (g32p_literalTraceValue 23 c)
      [1, -1, 1] (g32p_row24_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row24_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_005
  · exact g32p_row24_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_010
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_031
  · exact g32p_row24_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_034
  · exact g32p_row24_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_037
  · exact g32p_row24_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_049
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_065
  · exact g32p_row24_tracePolynomial_066
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_075
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_082
  · exact g32p_row24_tracePolynomial_083
  · exact g32p_row24_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_086
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_096
  · exact g32p_row24_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup19_support) hc)
  · exact g32p_row24_tracePolynomial_101

theorem g32p_row24_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 23 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 23 c) := by
  by_cases hc : c ∈ g32p_supplierGroup19_support
  · have hclass (j : Fin 1152) :
        IsConj (g32p_literalRepresentative c) (g32p_row24_groupEquiv j : g32p_G) ↔
          g32p_row24_supplierClassifier j = c := by
      simpa only [g32p_row24_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row24_supplierClass_iff (g32p_row24_groupEquiv j) c
    have hχ (j : Fin 1152) :
        (g32p_recordedSupplierCharacters 23 (g32p_row24_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row24_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 23 (show (g32p_recordedSuppliers 23).H from g32p_row24_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row24_characterValues (g32p_row24_groupEquiv.symm (g32p_row24_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 23).H (g32p_recordedSupplierCharacters 23)
      (g32p_literalRepresentative c) g32p_row24_groupEquiv g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) c 6 1152
      (g32p_literalCentralizer c) (g32p_literalTraceValue 23 c) [1, -1, 1]
      (g32p_row24_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row24_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 23)))
      (g32p_row24_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row24_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row24_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row24_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row24_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 23 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
