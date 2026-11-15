import HodgeLean.Foundations.Program.G32PropFourSixPacked0401
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0403
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0402
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_089 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 89 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_089_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 0 9 9, g32p_row26_traceSegment_089_0000_0009, g32p_row26_traceSegment_089_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 18 9 9, g32p_row26_traceSegment_089_0018_0009, g32p_row26_traceSegment_089_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 0 18 18, g32p_row26_traceSegment_089_0000_0018, g32p_row26_traceSegment_089_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 45 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 36 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 36 9 9, g32p_row26_traceSegment_089_0036_0009, g32p_row26_traceSegment_089_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 54 9 9, g32p_row26_traceSegment_089_0054_0009, g32p_row26_traceSegment_089_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 36 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 36 18 18, g32p_row26_traceSegment_089_0036_0018, g32p_row26_traceSegment_089_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 0 36 36, g32p_row26_traceSegment_089_0000_0036, g32p_row26_traceSegment_089_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 72 9 9, g32p_row26_traceSegment_089_0072_0009, g32p_row26_traceSegment_089_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 90 9 9, g32p_row26_traceSegment_089_0090_0009, g32p_row26_traceSegment_089_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 72 18 18, g32p_row26_traceSegment_089_0072_0018, g32p_row26_traceSegment_089_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 108 9 9, g32p_row26_traceSegment_089_0108_0009, g32p_row26_traceSegment_089_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 126 9 9, g32p_row26_traceSegment_089_0126_0009, g32p_row26_traceSegment_089_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 108 18 18, g32p_row26_traceSegment_089_0108_0018, g32p_row26_traceSegment_089_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 72 36 36, g32p_row26_traceSegment_089_0072_0036, g32p_row26_traceSegment_089_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_089 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 0 72 72, g32p_row26_traceSegment_089_0000_0072, g32p_row26_traceSegment_089_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 144 9 9, g32p_row26_traceSegment_089_0144_0009, g32p_row26_traceSegment_089_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 162 9 9, g32p_row26_traceSegment_089_0162_0009, g32p_row26_traceSegment_089_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 144 18 18, g32p_row26_traceSegment_089_0144_0018, g32p_row26_traceSegment_089_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 180 9 9, g32p_row26_traceSegment_089_0180_0009, g32p_row26_traceSegment_089_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 198 9 9, g32p_row26_traceSegment_089_0198_0009, g32p_row26_traceSegment_089_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 180 18 18, g32p_row26_traceSegment_089_0180_0018, g32p_row26_traceSegment_089_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 144 36 36, g32p_row26_traceSegment_089_0144_0036, g32p_row26_traceSegment_089_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 216 9 9, g32p_row26_traceSegment_089_0216_0009, g32p_row26_traceSegment_089_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 234 9 9, g32p_row26_traceSegment_089_0234_0009, g32p_row26_traceSegment_089_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 216 18 18, g32p_row26_traceSegment_089_0216_0018, g32p_row26_traceSegment_089_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 252 9 9, g32p_row26_traceSegment_089_0252_0009, g32p_row26_traceSegment_089_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 270 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 270 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 270 9 9, g32p_row26_traceSegment_089_0270_0009, g32p_row26_traceSegment_089_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 252 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 252 18 18, g32p_row26_traceSegment_089_0252_0018, g32p_row26_traceSegment_089_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 216 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 216 36 36, g32p_row26_traceSegment_089_0216_0036, g32p_row26_traceSegment_089_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_089 144 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 144 72 72, g32p_row26_traceSegment_089_0144_0072, g32p_row26_traceSegment_089_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_089 0 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 0 144 144, g32p_row26_traceSegment_089_0000_0144, g32p_row26_traceSegment_089_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 288 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 288 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 288 9 9, g32p_row26_traceSegment_089_0288_0009, g32p_row26_traceSegment_089_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 306 9 9, g32p_row26_traceSegment_089_0306_0009, g32p_row26_traceSegment_089_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 288 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 288 18 18, g32p_row26_traceSegment_089_0288_0018, g32p_row26_traceSegment_089_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 324 9 9, g32p_row26_traceSegment_089_0324_0009, g32p_row26_traceSegment_089_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 342 9 9, g32p_row26_traceSegment_089_0342_0009, g32p_row26_traceSegment_089_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 324 18 18, g32p_row26_traceSegment_089_0324_0018, g32p_row26_traceSegment_089_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 288 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 288 36 36, g32p_row26_traceSegment_089_0288_0036, g32p_row26_traceSegment_089_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 360 9 9, g32p_row26_traceSegment_089_0360_0009, g32p_row26_traceSegment_089_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 378 9 9, g32p_row26_traceSegment_089_0378_0009, g32p_row26_traceSegment_089_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 360 18 18, g32p_row26_traceSegment_089_0360_0018, g32p_row26_traceSegment_089_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 396 9 9, g32p_row26_traceSegment_089_0396_0009, g32p_row26_traceSegment_089_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 414 9 9, g32p_row26_traceSegment_089_0414_0009, g32p_row26_traceSegment_089_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 396 18 18, g32p_row26_traceSegment_089_0396_0018, g32p_row26_traceSegment_089_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 360 36 36, g32p_row26_traceSegment_089_0360_0036, g32p_row26_traceSegment_089_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_089 288 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 288 72 72, g32p_row26_traceSegment_089_0288_0072, g32p_row26_traceSegment_089_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 432 9 9, g32p_row26_traceSegment_089_0432_0009, g32p_row26_traceSegment_089_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 450 9 9, g32p_row26_traceSegment_089_0450_0009, g32p_row26_traceSegment_089_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 432 18 18, g32p_row26_traceSegment_089_0432_0018, g32p_row26_traceSegment_089_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 468 9 9, g32p_row26_traceSegment_089_0468_0009, g32p_row26_traceSegment_089_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 486 9 9, g32p_row26_traceSegment_089_0486_0009, g32p_row26_traceSegment_089_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 468 18 18, g32p_row26_traceSegment_089_0468_0018, g32p_row26_traceSegment_089_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 432 36 36, g32p_row26_traceSegment_089_0432_0036, g32p_row26_traceSegment_089_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 504 9 9, g32p_row26_traceSegment_089_0504_0009, g32p_row26_traceSegment_089_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 531 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 522 9 9, g32p_row26_traceSegment_089_0522_0009, g32p_row26_traceSegment_089_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 504 18 18, g32p_row26_traceSegment_089_0504_0018, g32p_row26_traceSegment_089_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 540 9 9, g32p_row26_traceSegment_089_0540_0009, g32p_row26_traceSegment_089_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_089 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_089_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_089 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 558 9 9, g32p_row26_traceSegment_089_0558_0009, g32p_row26_traceSegment_089_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_089 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 540 18 18, g32p_row26_traceSegment_089_0540_0018, g32p_row26_traceSegment_089_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_089 504 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 504 36 36, g32p_row26_traceSegment_089_0504_0036, g32p_row26_traceSegment_089_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_089 432 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 432 72 72, g32p_row26_traceSegment_089_0432_0072, g32p_row26_traceSegment_089_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_089 288 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 288 144 144, g32p_row26_traceSegment_089_0288_0144, g32p_row26_traceSegment_089_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_089_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_089 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_089 0 288 288, g32p_row26_traceSegment_089_0000_0288, g32p_row26_traceSegment_089_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 89 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_089_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_090 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 90 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_090_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 0 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 0 9 9, g32p_row26_traceSegment_090_0000_0009, g32p_row26_traceSegment_090_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 18 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 18 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 18 9 9, g32p_row26_traceSegment_090_0018_0009, g32p_row26_traceSegment_090_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 0 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 0 18 18, g32p_row26_traceSegment_090_0000_0018, g32p_row26_traceSegment_090_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 36 9 9, g32p_row26_traceSegment_090_0036_0009, g32p_row26_traceSegment_090_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 54 9 9, g32p_row26_traceSegment_090_0054_0009, g32p_row26_traceSegment_090_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 36 18 18, g32p_row26_traceSegment_090_0036_0018, g32p_row26_traceSegment_090_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 0 72 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 0 36 36, g32p_row26_traceSegment_090_0000_0036, g32p_row26_traceSegment_090_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 72 9 9, g32p_row26_traceSegment_090_0072_0009, g32p_row26_traceSegment_090_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 90 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 99 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 90 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 90 9 9, g32p_row26_traceSegment_090_0090_0009, g32p_row26_traceSegment_090_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 72 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 72 18 18, g32p_row26_traceSegment_090_0072_0018, g32p_row26_traceSegment_090_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 108 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 108 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 108 9 9, g32p_row26_traceSegment_090_0108_0009, g32p_row26_traceSegment_090_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 126 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 135 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 126 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 126 9 9, g32p_row26_traceSegment_090_0126_0009, g32p_row26_traceSegment_090_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 108 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 108 18 18, g32p_row26_traceSegment_090_0108_0018, g32p_row26_traceSegment_090_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 72 72 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 72 36 36, g32p_row26_traceSegment_090_0072_0036, g32p_row26_traceSegment_090_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_090 0 144 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 0 72 72, g32p_row26_traceSegment_090_0000_0072, g32p_row26_traceSegment_090_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 144 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 153 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 144 18 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 144 9 9, g32p_row26_traceSegment_090_0144_0009, g32p_row26_traceSegment_090_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 162 9 9, g32p_row26_traceSegment_090_0162_0009, g32p_row26_traceSegment_090_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 144 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 144 18 18, g32p_row26_traceSegment_090_0144_0018, g32p_row26_traceSegment_090_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 180 9 9, g32p_row26_traceSegment_090_0180_0009, g32p_row26_traceSegment_090_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 198 9 9, g32p_row26_traceSegment_090_0198_0009, g32p_row26_traceSegment_090_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 180 18 18, g32p_row26_traceSegment_090_0180_0018, g32p_row26_traceSegment_090_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 144 72 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 144 36 36, g32p_row26_traceSegment_090_0144_0036, g32p_row26_traceSegment_090_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 216 9 9, g32p_row26_traceSegment_090_0216_0009, g32p_row26_traceSegment_090_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 234 9 9, g32p_row26_traceSegment_090_0234_0009, g32p_row26_traceSegment_090_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 216 18 18, g32p_row26_traceSegment_090_0216_0018, g32p_row26_traceSegment_090_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 252 9 9, g32p_row26_traceSegment_090_0252_0009, g32p_row26_traceSegment_090_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 270 9 9, g32p_row26_traceSegment_090_0270_0009, g32p_row26_traceSegment_090_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 252 18 18, g32p_row26_traceSegment_090_0252_0018, g32p_row26_traceSegment_090_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 216 36 36, g32p_row26_traceSegment_090_0216_0036, g32p_row26_traceSegment_090_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_090 144 144 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 144 72 72, g32p_row26_traceSegment_090_0144_0072, g32p_row26_traceSegment_090_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_090 0 288 = [0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 0 144 144, g32p_row26_traceSegment_090_0000_0144, g32p_row26_traceSegment_090_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 288 9 9, g32p_row26_traceSegment_090_0288_0009, g32p_row26_traceSegment_090_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 306 9 9, g32p_row26_traceSegment_090_0306_0009, g32p_row26_traceSegment_090_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 288 18 18, g32p_row26_traceSegment_090_0288_0018, g32p_row26_traceSegment_090_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 324 9 9, g32p_row26_traceSegment_090_0324_0009, g32p_row26_traceSegment_090_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 342 9 9, g32p_row26_traceSegment_090_0342_0009, g32p_row26_traceSegment_090_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 324 18 18, g32p_row26_traceSegment_090_0324_0018, g32p_row26_traceSegment_090_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 288 36 36, g32p_row26_traceSegment_090_0288_0036, g32p_row26_traceSegment_090_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 360 9 9, g32p_row26_traceSegment_090_0360_0009, g32p_row26_traceSegment_090_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 378 9 9, g32p_row26_traceSegment_090_0378_0009, g32p_row26_traceSegment_090_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 360 18 18, g32p_row26_traceSegment_090_0360_0018, g32p_row26_traceSegment_090_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 396 9 9, g32p_row26_traceSegment_090_0396_0009, g32p_row26_traceSegment_090_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 414 9 9, g32p_row26_traceSegment_090_0414_0009, g32p_row26_traceSegment_090_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 396 18 18, g32p_row26_traceSegment_090_0396_0018, g32p_row26_traceSegment_090_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 360 36 36, g32p_row26_traceSegment_090_0360_0036, g32p_row26_traceSegment_090_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_090 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 288 72 72, g32p_row26_traceSegment_090_0288_0072, g32p_row26_traceSegment_090_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 432 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 432 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 432 9 9, g32p_row26_traceSegment_090_0432_0009, g32p_row26_traceSegment_090_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 450 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 450 9 9, g32p_row26_traceSegment_090_0450_0009, g32p_row26_traceSegment_090_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 432 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 432 18 18, g32p_row26_traceSegment_090_0432_0018, g32p_row26_traceSegment_090_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 468 9 9, g32p_row26_traceSegment_090_0468_0009, g32p_row26_traceSegment_090_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 486 9 9, g32p_row26_traceSegment_090_0486_0009, g32p_row26_traceSegment_090_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 468 18 18, g32p_row26_traceSegment_090_0468_0018, g32p_row26_traceSegment_090_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 432 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 432 36 36, g32p_row26_traceSegment_090_0432_0036, g32p_row26_traceSegment_090_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 504 9 9, g32p_row26_traceSegment_090_0504_0009, g32p_row26_traceSegment_090_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 522 9 9, g32p_row26_traceSegment_090_0522_0009, g32p_row26_traceSegment_090_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 504 18 18, g32p_row26_traceSegment_090_0504_0018, g32p_row26_traceSegment_090_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 540 9 9, g32p_row26_traceSegment_090_0540_0009, g32p_row26_traceSegment_090_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_090 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_090_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_090 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 558 9 9, g32p_row26_traceSegment_090_0558_0009, g32p_row26_traceSegment_090_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_090 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 540 18 18, g32p_row26_traceSegment_090_0540_0018, g32p_row26_traceSegment_090_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_090 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 504 36 36, g32p_row26_traceSegment_090_0504_0036, g32p_row26_traceSegment_090_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_090 432 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 432 72 72, g32p_row26_traceSegment_090_0432_0072, g32p_row26_traceSegment_090_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_090 288 288 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 288 144 144, g32p_row26_traceSegment_090_0288_0144, g32p_row26_traceSegment_090_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_090_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_090 0 576 = [0, 4, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_090 0 288 288, g32p_row26_traceSegment_090_0000_0288, g32p_row26_traceSegment_090_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 90 = [0, 4, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_090_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_091 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 91 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_091_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 0 9 9, g32p_row26_traceSegment_091_0000_0009, g32p_row26_traceSegment_091_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 18 9 9, g32p_row26_traceSegment_091_0018_0009, g32p_row26_traceSegment_091_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 0 18 18, g32p_row26_traceSegment_091_0000_0018, g32p_row26_traceSegment_091_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 36 9 9, g32p_row26_traceSegment_091_0036_0009, g32p_row26_traceSegment_091_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 54 9 9, g32p_row26_traceSegment_091_0054_0009, g32p_row26_traceSegment_091_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 36 18 18, g32p_row26_traceSegment_091_0036_0018, g32p_row26_traceSegment_091_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 0 36 36, g32p_row26_traceSegment_091_0000_0036, g32p_row26_traceSegment_091_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 72 9 9, g32p_row26_traceSegment_091_0072_0009, g32p_row26_traceSegment_091_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 90 9 9, g32p_row26_traceSegment_091_0090_0009, g32p_row26_traceSegment_091_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 72 18 18, g32p_row26_traceSegment_091_0072_0018, g32p_row26_traceSegment_091_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 108 9 9, g32p_row26_traceSegment_091_0108_0009, g32p_row26_traceSegment_091_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 126 9 9, g32p_row26_traceSegment_091_0126_0009, g32p_row26_traceSegment_091_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 108 18 18, g32p_row26_traceSegment_091_0108_0018, g32p_row26_traceSegment_091_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 72 36 36, g32p_row26_traceSegment_091_0072_0036, g32p_row26_traceSegment_091_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_091 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 0 72 72, g32p_row26_traceSegment_091_0000_0072, g32p_row26_traceSegment_091_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 144 9 9, g32p_row26_traceSegment_091_0144_0009, g32p_row26_traceSegment_091_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 162 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 171 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 162 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 162 9 9, g32p_row26_traceSegment_091_0162_0009, g32p_row26_traceSegment_091_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 144 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 144 18 18, g32p_row26_traceSegment_091_0144_0018, g32p_row26_traceSegment_091_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 180 9 9, g32p_row26_traceSegment_091_0180_0009, g32p_row26_traceSegment_091_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 198 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 198 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 198 9 9, g32p_row26_traceSegment_091_0198_0009, g32p_row26_traceSegment_091_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 180 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 180 18 18, g32p_row26_traceSegment_091_0180_0018, g32p_row26_traceSegment_091_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 144 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 144 36 36, g32p_row26_traceSegment_091_0144_0036, g32p_row26_traceSegment_091_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 216 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 216 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 216 9 9, g32p_row26_traceSegment_091_0216_0009, g32p_row26_traceSegment_091_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 234 9 9, g32p_row26_traceSegment_091_0234_0009, g32p_row26_traceSegment_091_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 216 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 216 18 18, g32p_row26_traceSegment_091_0216_0018, g32p_row26_traceSegment_091_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 252 9 9, g32p_row26_traceSegment_091_0252_0009, g32p_row26_traceSegment_091_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 270 9 9, g32p_row26_traceSegment_091_0270_0009, g32p_row26_traceSegment_091_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 252 18 18, g32p_row26_traceSegment_091_0252_0018, g32p_row26_traceSegment_091_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 216 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 216 36 36, g32p_row26_traceSegment_091_0216_0036, g32p_row26_traceSegment_091_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_091 144 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 144 72 72, g32p_row26_traceSegment_091_0144_0072, g32p_row26_traceSegment_091_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_091 0 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 0 144 144, g32p_row26_traceSegment_091_0000_0144, g32p_row26_traceSegment_091_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 288 9 9, g32p_row26_traceSegment_091_0288_0009, g32p_row26_traceSegment_091_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 306 9 9, g32p_row26_traceSegment_091_0306_0009, g32p_row26_traceSegment_091_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 288 18 18, g32p_row26_traceSegment_091_0288_0018, g32p_row26_traceSegment_091_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 324 9 9, g32p_row26_traceSegment_091_0324_0009, g32p_row26_traceSegment_091_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 342 9 9, g32p_row26_traceSegment_091_0342_0009, g32p_row26_traceSegment_091_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 324 18 18, g32p_row26_traceSegment_091_0324_0018, g32p_row26_traceSegment_091_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 288 36 36, g32p_row26_traceSegment_091_0288_0036, g32p_row26_traceSegment_091_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 360 9 9, g32p_row26_traceSegment_091_0360_0009, g32p_row26_traceSegment_091_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 378 9 9, g32p_row26_traceSegment_091_0378_0009, g32p_row26_traceSegment_091_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 360 18 18, g32p_row26_traceSegment_091_0360_0018, g32p_row26_traceSegment_091_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 396 9 9, g32p_row26_traceSegment_091_0396_0009, g32p_row26_traceSegment_091_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 414 9 9, g32p_row26_traceSegment_091_0414_0009, g32p_row26_traceSegment_091_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 396 18 18, g32p_row26_traceSegment_091_0396_0018, g32p_row26_traceSegment_091_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 360 36 36, g32p_row26_traceSegment_091_0360_0036, g32p_row26_traceSegment_091_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_091 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 288 72 72, g32p_row26_traceSegment_091_0288_0072, g32p_row26_traceSegment_091_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 432 9 9, g32p_row26_traceSegment_091_0432_0009, g32p_row26_traceSegment_091_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 450 9 9, g32p_row26_traceSegment_091_0450_0009, g32p_row26_traceSegment_091_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 432 18 18, g32p_row26_traceSegment_091_0432_0018, g32p_row26_traceSegment_091_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 468 9 9, g32p_row26_traceSegment_091_0468_0009, g32p_row26_traceSegment_091_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 486 9 9, g32p_row26_traceSegment_091_0486_0009, g32p_row26_traceSegment_091_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 468 18 18, g32p_row26_traceSegment_091_0468_0018, g32p_row26_traceSegment_091_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 432 36 36, g32p_row26_traceSegment_091_0432_0036, g32p_row26_traceSegment_091_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 504 9 9, g32p_row26_traceSegment_091_0504_0009, g32p_row26_traceSegment_091_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 522 9 9, g32p_row26_traceSegment_091_0522_0009, g32p_row26_traceSegment_091_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 504 18 18, g32p_row26_traceSegment_091_0504_0018, g32p_row26_traceSegment_091_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 540 9 9, g32p_row26_traceSegment_091_0540_0009, g32p_row26_traceSegment_091_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_091 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_091_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_091 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 558 9 9, g32p_row26_traceSegment_091_0558_0009, g32p_row26_traceSegment_091_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_091 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 540 18 18, g32p_row26_traceSegment_091_0540_0018, g32p_row26_traceSegment_091_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_091 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 504 36 36, g32p_row26_traceSegment_091_0504_0036, g32p_row26_traceSegment_091_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_091 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 432 72 72, g32p_row26_traceSegment_091_0432_0072, g32p_row26_traceSegment_091_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_091 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 288 144 144, g32p_row26_traceSegment_091_0288_0144, g32p_row26_traceSegment_091_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_091_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_091 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_091 0 288 288, g32p_row26_traceSegment_091_0000_0288, g32p_row26_traceSegment_091_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 91 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_091_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_093_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 0 9 9, g32p_row26_traceSegment_093_0000_0009, g32p_row26_traceSegment_093_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 18 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 18 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 18 9 9, g32p_row26_traceSegment_093_0018_0009, g32p_row26_traceSegment_093_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 0 18 18, g32p_row26_traceSegment_093_0000_0018, g32p_row26_traceSegment_093_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 36 9 9, g32p_row26_traceSegment_093_0036_0009, g32p_row26_traceSegment_093_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 54 9 9, g32p_row26_traceSegment_093_0054_0009, g32p_row26_traceSegment_093_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 36 18 18, g32p_row26_traceSegment_093_0036_0018, g32p_row26_traceSegment_093_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 0 36 36, g32p_row26_traceSegment_093_0000_0036, g32p_row26_traceSegment_093_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 72 9 9, g32p_row26_traceSegment_093_0072_0009, g32p_row26_traceSegment_093_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 90 9 9, g32p_row26_traceSegment_093_0090_0009, g32p_row26_traceSegment_093_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 72 18 18, g32p_row26_traceSegment_093_0072_0018, g32p_row26_traceSegment_093_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 108 9 9, g32p_row26_traceSegment_093_0108_0009, g32p_row26_traceSegment_093_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 126 9 9, g32p_row26_traceSegment_093_0126_0009, g32p_row26_traceSegment_093_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 108 18 18, g32p_row26_traceSegment_093_0108_0018, g32p_row26_traceSegment_093_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 72 36 36, g32p_row26_traceSegment_093_0072_0036, g32p_row26_traceSegment_093_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_093 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 0 72 72, g32p_row26_traceSegment_093_0000_0072, g32p_row26_traceSegment_093_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 144 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 144 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 144 9 9, g32p_row26_traceSegment_093_0144_0009, g32p_row26_traceSegment_093_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 162 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 171 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 162 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 162 9 9, g32p_row26_traceSegment_093_0162_0009, g32p_row26_traceSegment_093_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 144 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 144 18 18, g32p_row26_traceSegment_093_0144_0018, g32p_row26_traceSegment_093_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 180 9 9, g32p_row26_traceSegment_093_0180_0009, g32p_row26_traceSegment_093_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 198 9 9, g32p_row26_traceSegment_093_0198_0009, g32p_row26_traceSegment_093_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 180 18 18, g32p_row26_traceSegment_093_0180_0018, g32p_row26_traceSegment_093_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 144 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 144 36 36, g32p_row26_traceSegment_093_0144_0036, g32p_row26_traceSegment_093_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 216 9 9, g32p_row26_traceSegment_093_0216_0009, g32p_row26_traceSegment_093_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 234 9 9, g32p_row26_traceSegment_093_0234_0009, g32p_row26_traceSegment_093_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 216 18 18, g32p_row26_traceSegment_093_0216_0018, g32p_row26_traceSegment_093_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 252 9 9, g32p_row26_traceSegment_093_0252_0009, g32p_row26_traceSegment_093_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 270 9 9, g32p_row26_traceSegment_093_0270_0009, g32p_row26_traceSegment_093_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 252 18 18, g32p_row26_traceSegment_093_0252_0018, g32p_row26_traceSegment_093_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 216 36 36, g32p_row26_traceSegment_093_0216_0036, g32p_row26_traceSegment_093_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_093 144 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 144 72 72, g32p_row26_traceSegment_093_0144_0072, g32p_row26_traceSegment_093_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_093 0 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 0 144 144, g32p_row26_traceSegment_093_0000_0144, g32p_row26_traceSegment_093_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 288 9 9, g32p_row26_traceSegment_093_0288_0009, g32p_row26_traceSegment_093_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 306 9 9, g32p_row26_traceSegment_093_0306_0009, g32p_row26_traceSegment_093_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 288 18 18, g32p_row26_traceSegment_093_0288_0018, g32p_row26_traceSegment_093_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 324 9 9, g32p_row26_traceSegment_093_0324_0009, g32p_row26_traceSegment_093_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 342 9 9, g32p_row26_traceSegment_093_0342_0009, g32p_row26_traceSegment_093_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 324 18 18, g32p_row26_traceSegment_093_0324_0018, g32p_row26_traceSegment_093_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 288 36 36, g32p_row26_traceSegment_093_0288_0036, g32p_row26_traceSegment_093_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 360 9 9, g32p_row26_traceSegment_093_0360_0009, g32p_row26_traceSegment_093_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 378 9 9, g32p_row26_traceSegment_093_0378_0009, g32p_row26_traceSegment_093_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 360 18 18, g32p_row26_traceSegment_093_0360_0018, g32p_row26_traceSegment_093_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 396 9 9, g32p_row26_traceSegment_093_0396_0009, g32p_row26_traceSegment_093_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 414 9 9, g32p_row26_traceSegment_093_0414_0009, g32p_row26_traceSegment_093_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 396 18 18, g32p_row26_traceSegment_093_0396_0018, g32p_row26_traceSegment_093_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 360 36 36, g32p_row26_traceSegment_093_0360_0036, g32p_row26_traceSegment_093_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_093 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 288 72 72, g32p_row26_traceSegment_093_0288_0072, g32p_row26_traceSegment_093_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 432 9 9, g32p_row26_traceSegment_093_0432_0009, g32p_row26_traceSegment_093_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 450 9 9, g32p_row26_traceSegment_093_0450_0009, g32p_row26_traceSegment_093_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 432 18 18, g32p_row26_traceSegment_093_0432_0018, g32p_row26_traceSegment_093_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 468 9 9, g32p_row26_traceSegment_093_0468_0009, g32p_row26_traceSegment_093_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 486 9 9, g32p_row26_traceSegment_093_0486_0009, g32p_row26_traceSegment_093_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 468 18 18, g32p_row26_traceSegment_093_0468_0018, g32p_row26_traceSegment_093_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 432 36 36, g32p_row26_traceSegment_093_0432_0036, g32p_row26_traceSegment_093_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 504 9 9, g32p_row26_traceSegment_093_0504_0009, g32p_row26_traceSegment_093_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 522 9 9, g32p_row26_traceSegment_093_0522_0009, g32p_row26_traceSegment_093_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 504 18 18, g32p_row26_traceSegment_093_0504_0018, g32p_row26_traceSegment_093_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 540 9 9, g32p_row26_traceSegment_093_0540_0009, g32p_row26_traceSegment_093_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_093 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_093_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_093 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 558 9 9, g32p_row26_traceSegment_093_0558_0009, g32p_row26_traceSegment_093_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_093 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 540 18 18, g32p_row26_traceSegment_093_0540_0018, g32p_row26_traceSegment_093_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_093 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 504 36 36, g32p_row26_traceSegment_093_0504_0036, g32p_row26_traceSegment_093_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_093 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 432 72 72, g32p_row26_traceSegment_093_0432_0072, g32p_row26_traceSegment_093_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_093 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 288 144 144, g32p_row26_traceSegment_093_0288_0144, g32p_row26_traceSegment_093_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_093_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_093 0 576 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_093 0 288 288, g32p_row26_traceSegment_093_0000_0288, g32p_row26_traceSegment_093_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 93 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_093_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_094 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 94 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_094_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 0 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 0 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 0 9 9, g32p_row26_traceSegment_094_0000_0009, g32p_row26_traceSegment_094_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 18 9 9, g32p_row26_traceSegment_094_0018_0009, g32p_row26_traceSegment_094_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 0 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 0 18 18, g32p_row26_traceSegment_094_0000_0018, g32p_row26_traceSegment_094_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 36 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 45 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 36 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 36 9 9, g32p_row26_traceSegment_094_0036_0009, g32p_row26_traceSegment_094_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 63 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 54 9 9, g32p_row26_traceSegment_094_0054_0009, g32p_row26_traceSegment_094_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 36 36 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 36 18 18, g32p_row26_traceSegment_094_0036_0018, g32p_row26_traceSegment_094_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 0 72 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 0 36 36, g32p_row26_traceSegment_094_0000_0036, g32p_row26_traceSegment_094_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 72 9 9, g32p_row26_traceSegment_094_0072_0009, g32p_row26_traceSegment_094_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 90 9 9, g32p_row26_traceSegment_094_0090_0009, g32p_row26_traceSegment_094_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 72 18 18, g32p_row26_traceSegment_094_0072_0018, g32p_row26_traceSegment_094_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 108 9 9, g32p_row26_traceSegment_094_0108_0009, g32p_row26_traceSegment_094_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 135 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 126 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 126 9 9, g32p_row26_traceSegment_094_0126_0009, g32p_row26_traceSegment_094_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 108 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 108 18 18, g32p_row26_traceSegment_094_0108_0018, g32p_row26_traceSegment_094_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 72 72 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 72 36 36, g32p_row26_traceSegment_094_0072_0036, g32p_row26_traceSegment_094_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_094 0 144 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 0 72 72, g32p_row26_traceSegment_094_0000_0072, g32p_row26_traceSegment_094_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 144 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 144 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 144 9 9, g32p_row26_traceSegment_094_0144_0009, g32p_row26_traceSegment_094_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 162 9 9, g32p_row26_traceSegment_094_0162_0009, g32p_row26_traceSegment_094_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 144 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 144 18 18, g32p_row26_traceSegment_094_0144_0018, g32p_row26_traceSegment_094_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 180 9 9, g32p_row26_traceSegment_094_0180_0009, g32p_row26_traceSegment_094_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 207 9 = [2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 198 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 198 9 9, g32p_row26_traceSegment_094_0198_0009, g32p_row26_traceSegment_094_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 180 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 180 18 18, g32p_row26_traceSegment_094_0180_0018, g32p_row26_traceSegment_094_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 144 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 144 36 36, g32p_row26_traceSegment_094_0144_0036, g32p_row26_traceSegment_094_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 216 9 9, g32p_row26_traceSegment_094_0216_0009, g32p_row26_traceSegment_094_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 234 9 9, g32p_row26_traceSegment_094_0234_0009, g32p_row26_traceSegment_094_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 216 18 18, g32p_row26_traceSegment_094_0216_0018, g32p_row26_traceSegment_094_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 252 9 9, g32p_row26_traceSegment_094_0252_0009, g32p_row26_traceSegment_094_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 270 9 9, g32p_row26_traceSegment_094_0270_0009, g32p_row26_traceSegment_094_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 252 18 18, g32p_row26_traceSegment_094_0252_0018, g32p_row26_traceSegment_094_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 216 36 36, g32p_row26_traceSegment_094_0216_0036, g32p_row26_traceSegment_094_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_094 144 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 144 72 72, g32p_row26_traceSegment_094_0144_0072, g32p_row26_traceSegment_094_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_094 0 288 = [4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 0 144 144, g32p_row26_traceSegment_094_0000_0144, g32p_row26_traceSegment_094_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 288 9 9, g32p_row26_traceSegment_094_0288_0009, g32p_row26_traceSegment_094_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 306 9 9, g32p_row26_traceSegment_094_0306_0009, g32p_row26_traceSegment_094_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 288 18 18, g32p_row26_traceSegment_094_0288_0018, g32p_row26_traceSegment_094_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 324 9 9, g32p_row26_traceSegment_094_0324_0009, g32p_row26_traceSegment_094_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 342 9 9, g32p_row26_traceSegment_094_0342_0009, g32p_row26_traceSegment_094_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 324 18 18, g32p_row26_traceSegment_094_0324_0018, g32p_row26_traceSegment_094_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 288 36 36, g32p_row26_traceSegment_094_0288_0036, g32p_row26_traceSegment_094_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 360 9 9, g32p_row26_traceSegment_094_0360_0009, g32p_row26_traceSegment_094_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 378 9 9, g32p_row26_traceSegment_094_0378_0009, g32p_row26_traceSegment_094_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 360 18 18, g32p_row26_traceSegment_094_0360_0018, g32p_row26_traceSegment_094_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 396 9 9, g32p_row26_traceSegment_094_0396_0009, g32p_row26_traceSegment_094_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 414 9 9, g32p_row26_traceSegment_094_0414_0009, g32p_row26_traceSegment_094_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 396 18 18, g32p_row26_traceSegment_094_0396_0018, g32p_row26_traceSegment_094_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 360 36 36, g32p_row26_traceSegment_094_0360_0036, g32p_row26_traceSegment_094_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_094 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 288 72 72, g32p_row26_traceSegment_094_0288_0072, g32p_row26_traceSegment_094_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 432 9 9, g32p_row26_traceSegment_094_0432_0009, g32p_row26_traceSegment_094_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 450 9 = [2] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 450 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 450 9 9, g32p_row26_traceSegment_094_0450_0009, g32p_row26_traceSegment_094_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 432 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 432 18 18, g32p_row26_traceSegment_094_0432_0018, g32p_row26_traceSegment_094_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 468 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 468 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 468 9 9, g32p_row26_traceSegment_094_0468_0009, g32p_row26_traceSegment_094_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 495 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 486 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 486 9 9, g32p_row26_traceSegment_094_0486_0009, g32p_row26_traceSegment_094_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 468 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 468 18 18, g32p_row26_traceSegment_094_0468_0018, g32p_row26_traceSegment_094_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 432 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 432 36 36, g32p_row26_traceSegment_094_0432_0036, g32p_row26_traceSegment_094_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 504 9 9, g32p_row26_traceSegment_094_0504_0009, g32p_row26_traceSegment_094_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 522 9 9, g32p_row26_traceSegment_094_0522_0009, g32p_row26_traceSegment_094_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 504 18 18, g32p_row26_traceSegment_094_0504_0018, g32p_row26_traceSegment_094_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 540 9 9, g32p_row26_traceSegment_094_0540_0009, g32p_row26_traceSegment_094_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_094 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_094_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_094 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 558 9 9, g32p_row26_traceSegment_094_0558_0009, g32p_row26_traceSegment_094_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_094 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 540 18 18, g32p_row26_traceSegment_094_0540_0018, g32p_row26_traceSegment_094_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_094 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 504 36 36, g32p_row26_traceSegment_094_0504_0036, g32p_row26_traceSegment_094_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_094 432 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 432 72 72, g32p_row26_traceSegment_094_0432_0072, g32p_row26_traceSegment_094_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_094 288 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 288 144 144, g32p_row26_traceSegment_094_0288_0144, g32p_row26_traceSegment_094_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_094_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_094 0 576 = [8, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_094 0 288 288, g32p_row26_traceSegment_094_0000_0288, g32p_row26_traceSegment_094_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 94 = [8, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_094_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_095_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 0 9 9, g32p_row26_traceSegment_095_0000_0009, g32p_row26_traceSegment_095_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 18 9 9, g32p_row26_traceSegment_095_0018_0009, g32p_row26_traceSegment_095_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 0 18 18, g32p_row26_traceSegment_095_0000_0018, g32p_row26_traceSegment_095_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 36 9 9, g32p_row26_traceSegment_095_0036_0009, g32p_row26_traceSegment_095_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 54 9 9, g32p_row26_traceSegment_095_0054_0009, g32p_row26_traceSegment_095_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 36 18 18, g32p_row26_traceSegment_095_0036_0018, g32p_row26_traceSegment_095_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 0 36 36, g32p_row26_traceSegment_095_0000_0036, g32p_row26_traceSegment_095_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 72 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 72 9 9, g32p_row26_traceSegment_095_0072_0009, g32p_row26_traceSegment_095_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 99 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 90 9 9, g32p_row26_traceSegment_095_0090_0009, g32p_row26_traceSegment_095_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 72 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 72 18 18, g32p_row26_traceSegment_095_0072_0018, g32p_row26_traceSegment_095_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 108 9 9, g32p_row26_traceSegment_095_0108_0009, g32p_row26_traceSegment_095_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 126 9 9, g32p_row26_traceSegment_095_0126_0009, g32p_row26_traceSegment_095_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 108 18 18, g32p_row26_traceSegment_095_0108_0018, g32p_row26_traceSegment_095_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 72 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 72 36 36, g32p_row26_traceSegment_095_0072_0036, g32p_row26_traceSegment_095_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_095 0 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 0 72 72, g32p_row26_traceSegment_095_0000_0072, g32p_row26_traceSegment_095_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 153 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 144 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 144 9 9, g32p_row26_traceSegment_095_0144_0009, g32p_row26_traceSegment_095_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 162 9 9, g32p_row26_traceSegment_095_0162_0009, g32p_row26_traceSegment_095_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 144 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 144 18 18, g32p_row26_traceSegment_095_0144_0018, g32p_row26_traceSegment_095_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 189 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 180 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 180 9 9, g32p_row26_traceSegment_095_0180_0009, g32p_row26_traceSegment_095_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 198 9 9, g32p_row26_traceSegment_095_0198_0009, g32p_row26_traceSegment_095_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 180 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 180 18 18, g32p_row26_traceSegment_095_0180_0018, g32p_row26_traceSegment_095_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 144 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 144 36 36, g32p_row26_traceSegment_095_0144_0036, g32p_row26_traceSegment_095_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 216 9 9, g32p_row26_traceSegment_095_0216_0009, g32p_row26_traceSegment_095_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 234 9 9, g32p_row26_traceSegment_095_0234_0009, g32p_row26_traceSegment_095_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 216 18 18, g32p_row26_traceSegment_095_0216_0018, g32p_row26_traceSegment_095_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 252 9 9, g32p_row26_traceSegment_095_0252_0009, g32p_row26_traceSegment_095_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 270 9 9, g32p_row26_traceSegment_095_0270_0009, g32p_row26_traceSegment_095_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 252 18 18, g32p_row26_traceSegment_095_0252_0018, g32p_row26_traceSegment_095_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 216 36 36, g32p_row26_traceSegment_095_0216_0036, g32p_row26_traceSegment_095_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_095 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 144 72 72, g32p_row26_traceSegment_095_0144_0072, g32p_row26_traceSegment_095_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_095 0 288 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 0 144 144, g32p_row26_traceSegment_095_0000_0144, g32p_row26_traceSegment_095_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 288 9 9, g32p_row26_traceSegment_095_0288_0009, g32p_row26_traceSegment_095_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 306 9 9, g32p_row26_traceSegment_095_0306_0009, g32p_row26_traceSegment_095_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 288 18 18, g32p_row26_traceSegment_095_0288_0018, g32p_row26_traceSegment_095_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 324 9 9, g32p_row26_traceSegment_095_0324_0009, g32p_row26_traceSegment_095_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 342 9 9, g32p_row26_traceSegment_095_0342_0009, g32p_row26_traceSegment_095_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 324 18 18, g32p_row26_traceSegment_095_0324_0018, g32p_row26_traceSegment_095_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 288 36 36, g32p_row26_traceSegment_095_0288_0036, g32p_row26_traceSegment_095_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 360 9 9, g32p_row26_traceSegment_095_0360_0009, g32p_row26_traceSegment_095_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 378 9 9, g32p_row26_traceSegment_095_0378_0009, g32p_row26_traceSegment_095_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 360 18 18, g32p_row26_traceSegment_095_0360_0018, g32p_row26_traceSegment_095_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 396 9 9, g32p_row26_traceSegment_095_0396_0009, g32p_row26_traceSegment_095_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 414 9 9, g32p_row26_traceSegment_095_0414_0009, g32p_row26_traceSegment_095_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 396 18 18, g32p_row26_traceSegment_095_0396_0018, g32p_row26_traceSegment_095_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 360 36 36, g32p_row26_traceSegment_095_0360_0036, g32p_row26_traceSegment_095_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_095 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 288 72 72, g32p_row26_traceSegment_095_0288_0072, g32p_row26_traceSegment_095_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 432 9 9, g32p_row26_traceSegment_095_0432_0009, g32p_row26_traceSegment_095_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 450 9 9, g32p_row26_traceSegment_095_0450_0009, g32p_row26_traceSegment_095_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 432 18 18, g32p_row26_traceSegment_095_0432_0018, g32p_row26_traceSegment_095_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 468 9 9, g32p_row26_traceSegment_095_0468_0009, g32p_row26_traceSegment_095_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 486 9 9, g32p_row26_traceSegment_095_0486_0009, g32p_row26_traceSegment_095_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 468 18 18, g32p_row26_traceSegment_095_0468_0018, g32p_row26_traceSegment_095_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 432 36 36, g32p_row26_traceSegment_095_0432_0036, g32p_row26_traceSegment_095_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 504 9 9, g32p_row26_traceSegment_095_0504_0009, g32p_row26_traceSegment_095_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 522 9 9, g32p_row26_traceSegment_095_0522_0009, g32p_row26_traceSegment_095_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 504 18 18, g32p_row26_traceSegment_095_0504_0018, g32p_row26_traceSegment_095_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 540 9 9, g32p_row26_traceSegment_095_0540_0009, g32p_row26_traceSegment_095_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_095 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_095_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_095 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 558 9 9, g32p_row26_traceSegment_095_0558_0009, g32p_row26_traceSegment_095_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_095 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 540 18 18, g32p_row26_traceSegment_095_0540_0018, g32p_row26_traceSegment_095_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_095 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 504 36 36, g32p_row26_traceSegment_095_0504_0036, g32p_row26_traceSegment_095_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_095 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 432 72 72, g32p_row26_traceSegment_095_0432_0072, g32p_row26_traceSegment_095_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_095 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 288 144 144, g32p_row26_traceSegment_095_0288_0144, g32p_row26_traceSegment_095_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_095_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_095 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_095 0 288 288, g32p_row26_traceSegment_095_0000_0288, g32p_row26_traceSegment_095_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 95 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_095_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 87) (g32p_literalTraceValue 25 87)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_087]
  decide +kernel

theorem g32p_row26_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 88) (g32p_literalTraceValue 25 88)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_088]
  decide +kernel

theorem g32p_row26_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 89) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 89) (g32p_literalTraceValue 25 89)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_089]
  decide +kernel

theorem g32p_row26_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 90) (g32p_literalTraceValue 25 90)
      [1, -1, 1] [1152, 2304, 2304] = true := by
  rw [g32p_row26_traceCoefficients_090]
  decide +kernel

theorem g32p_row26_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 91) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 91) (g32p_literalTraceValue 25 91)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_091]
  decide +kernel

theorem g32p_row26_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 93) (g32p_literalTraceValue 25 93)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_093]
  decide +kernel

theorem g32p_row26_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 94) (g32p_literalTraceValue 25 94)
      [1, -1, 1] [1152, 1152] = true := by
  rw [g32p_row26_traceCoefficients_094]
  decide +kernel

theorem g32p_row26_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 95) (g32p_literalTraceValue 25 95)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row26_traceCoefficients_095]
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

private def g32p_row26_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_096_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 0 9 9, g32p_row26_traceSegment_096_0000_0009, g32p_row26_traceSegment_096_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 18 9 9, g32p_row26_traceSegment_096_0018_0009, g32p_row26_traceSegment_096_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 0 18 18, g32p_row26_traceSegment_096_0000_0018, g32p_row26_traceSegment_096_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 36 9 9, g32p_row26_traceSegment_096_0036_0009, g32p_row26_traceSegment_096_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 54 9 9, g32p_row26_traceSegment_096_0054_0009, g32p_row26_traceSegment_096_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 36 18 18, g32p_row26_traceSegment_096_0036_0018, g32p_row26_traceSegment_096_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 0 36 36, g32p_row26_traceSegment_096_0000_0036, g32p_row26_traceSegment_096_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 72 9 9, g32p_row26_traceSegment_096_0072_0009, g32p_row26_traceSegment_096_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 90 9 9, g32p_row26_traceSegment_096_0090_0009, g32p_row26_traceSegment_096_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 72 18 18, g32p_row26_traceSegment_096_0072_0018, g32p_row26_traceSegment_096_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 108 9 9, g32p_row26_traceSegment_096_0108_0009, g32p_row26_traceSegment_096_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 126 9 9, g32p_row26_traceSegment_096_0126_0009, g32p_row26_traceSegment_096_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 108 18 18, g32p_row26_traceSegment_096_0108_0018, g32p_row26_traceSegment_096_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 72 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 72 36 36, g32p_row26_traceSegment_096_0072_0036, g32p_row26_traceSegment_096_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_096 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 0 72 72, g32p_row26_traceSegment_096_0000_0072, g32p_row26_traceSegment_096_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 144 9 9, g32p_row26_traceSegment_096_0144_0009, g32p_row26_traceSegment_096_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 162 9 9, g32p_row26_traceSegment_096_0162_0009, g32p_row26_traceSegment_096_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 144 18 18, g32p_row26_traceSegment_096_0144_0018, g32p_row26_traceSegment_096_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 180 9 9, g32p_row26_traceSegment_096_0180_0009, g32p_row26_traceSegment_096_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 198 9 9, g32p_row26_traceSegment_096_0198_0009, g32p_row26_traceSegment_096_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 180 18 18, g32p_row26_traceSegment_096_0180_0018, g32p_row26_traceSegment_096_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 144 36 36, g32p_row26_traceSegment_096_0144_0036, g32p_row26_traceSegment_096_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 216 9 9, g32p_row26_traceSegment_096_0216_0009, g32p_row26_traceSegment_096_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 234 9 9, g32p_row26_traceSegment_096_0234_0009, g32p_row26_traceSegment_096_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 216 18 18, g32p_row26_traceSegment_096_0216_0018, g32p_row26_traceSegment_096_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 252 9 9, g32p_row26_traceSegment_096_0252_0009, g32p_row26_traceSegment_096_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 270 9 9, g32p_row26_traceSegment_096_0270_0009, g32p_row26_traceSegment_096_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 252 18 18, g32p_row26_traceSegment_096_0252_0018, g32p_row26_traceSegment_096_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 216 36 36, g32p_row26_traceSegment_096_0216_0036, g32p_row26_traceSegment_096_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_096 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 144 72 72, g32p_row26_traceSegment_096_0144_0072, g32p_row26_traceSegment_096_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_096 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 0 144 144, g32p_row26_traceSegment_096_0000_0144, g32p_row26_traceSegment_096_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 288 9 9, g32p_row26_traceSegment_096_0288_0009, g32p_row26_traceSegment_096_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 306 9 9, g32p_row26_traceSegment_096_0306_0009, g32p_row26_traceSegment_096_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 288 18 18, g32p_row26_traceSegment_096_0288_0018, g32p_row26_traceSegment_096_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 324 9 9, g32p_row26_traceSegment_096_0324_0009, g32p_row26_traceSegment_096_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 342 9 9, g32p_row26_traceSegment_096_0342_0009, g32p_row26_traceSegment_096_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 324 18 18, g32p_row26_traceSegment_096_0324_0018, g32p_row26_traceSegment_096_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 288 36 36, g32p_row26_traceSegment_096_0288_0036, g32p_row26_traceSegment_096_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 360 9 9, g32p_row26_traceSegment_096_0360_0009, g32p_row26_traceSegment_096_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 378 9 9, g32p_row26_traceSegment_096_0378_0009, g32p_row26_traceSegment_096_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 360 18 18, g32p_row26_traceSegment_096_0360_0018, g32p_row26_traceSegment_096_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 396 9 9, g32p_row26_traceSegment_096_0396_0009, g32p_row26_traceSegment_096_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 414 9 9, g32p_row26_traceSegment_096_0414_0009, g32p_row26_traceSegment_096_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 396 18 18, g32p_row26_traceSegment_096_0396_0018, g32p_row26_traceSegment_096_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 360 36 36, g32p_row26_traceSegment_096_0360_0036, g32p_row26_traceSegment_096_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_096 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 288 72 72, g32p_row26_traceSegment_096_0288_0072, g32p_row26_traceSegment_096_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 432 9 9, g32p_row26_traceSegment_096_0432_0009, g32p_row26_traceSegment_096_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 450 9 9, g32p_row26_traceSegment_096_0450_0009, g32p_row26_traceSegment_096_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 432 18 18, g32p_row26_traceSegment_096_0432_0018, g32p_row26_traceSegment_096_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 468 9 9, g32p_row26_traceSegment_096_0468_0009, g32p_row26_traceSegment_096_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 486 9 9, g32p_row26_traceSegment_096_0486_0009, g32p_row26_traceSegment_096_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 468 18 18, g32p_row26_traceSegment_096_0468_0018, g32p_row26_traceSegment_096_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 432 36 36, g32p_row26_traceSegment_096_0432_0036, g32p_row26_traceSegment_096_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 504 9 9, g32p_row26_traceSegment_096_0504_0009, g32p_row26_traceSegment_096_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 522 9 9, g32p_row26_traceSegment_096_0522_0009, g32p_row26_traceSegment_096_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 504 18 18, g32p_row26_traceSegment_096_0504_0018, g32p_row26_traceSegment_096_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 540 9 9, g32p_row26_traceSegment_096_0540_0009, g32p_row26_traceSegment_096_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_096 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_096_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_096 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 558 9 9, g32p_row26_traceSegment_096_0558_0009, g32p_row26_traceSegment_096_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_096 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 540 18 18, g32p_row26_traceSegment_096_0540_0018, g32p_row26_traceSegment_096_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_096 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 504 36 36, g32p_row26_traceSegment_096_0504_0036, g32p_row26_traceSegment_096_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_096 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 432 72 72, g32p_row26_traceSegment_096_0432_0072, g32p_row26_traceSegment_096_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_096 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 288 144 144, g32p_row26_traceSegment_096_0288_0144, g32p_row26_traceSegment_096_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_096_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_096 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_096 0 288 288, g32p_row26_traceSegment_096_0000_0288, g32p_row26_traceSegment_096_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_096_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_097_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 0 9 9, g32p_row26_traceSegment_097_0000_0009, g32p_row26_traceSegment_097_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 18 9 9, g32p_row26_traceSegment_097_0018_0009, g32p_row26_traceSegment_097_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 0 18 18, g32p_row26_traceSegment_097_0000_0018, g32p_row26_traceSegment_097_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 36 9 9, g32p_row26_traceSegment_097_0036_0009, g32p_row26_traceSegment_097_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 63 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 54 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 54 9 9, g32p_row26_traceSegment_097_0054_0009, g32p_row26_traceSegment_097_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 36 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 36 18 18, g32p_row26_traceSegment_097_0036_0018, g32p_row26_traceSegment_097_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 0 36 36, g32p_row26_traceSegment_097_0000_0036, g32p_row26_traceSegment_097_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 72 9 9, g32p_row26_traceSegment_097_0072_0009, g32p_row26_traceSegment_097_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 90 9 9, g32p_row26_traceSegment_097_0090_0009, g32p_row26_traceSegment_097_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 72 18 18, g32p_row26_traceSegment_097_0072_0018, g32p_row26_traceSegment_097_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 108 9 9, g32p_row26_traceSegment_097_0108_0009, g32p_row26_traceSegment_097_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 126 9 9, g32p_row26_traceSegment_097_0126_0009, g32p_row26_traceSegment_097_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 108 18 18, g32p_row26_traceSegment_097_0108_0018, g32p_row26_traceSegment_097_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 72 36 36, g32p_row26_traceSegment_097_0072_0036, g32p_row26_traceSegment_097_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_097 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 0 72 72, g32p_row26_traceSegment_097_0000_0072, g32p_row26_traceSegment_097_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 144 9 9, g32p_row26_traceSegment_097_0144_0009, g32p_row26_traceSegment_097_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 162 9 9, g32p_row26_traceSegment_097_0162_0009, g32p_row26_traceSegment_097_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 144 18 18, g32p_row26_traceSegment_097_0144_0018, g32p_row26_traceSegment_097_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 180 9 9, g32p_row26_traceSegment_097_0180_0009, g32p_row26_traceSegment_097_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 198 9 9, g32p_row26_traceSegment_097_0198_0009, g32p_row26_traceSegment_097_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 180 18 18, g32p_row26_traceSegment_097_0180_0018, g32p_row26_traceSegment_097_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 144 36 36, g32p_row26_traceSegment_097_0144_0036, g32p_row26_traceSegment_097_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 216 9 9, g32p_row26_traceSegment_097_0216_0009, g32p_row26_traceSegment_097_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 234 9 9, g32p_row26_traceSegment_097_0234_0009, g32p_row26_traceSegment_097_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 216 18 18, g32p_row26_traceSegment_097_0216_0018, g32p_row26_traceSegment_097_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 252 9 9, g32p_row26_traceSegment_097_0252_0009, g32p_row26_traceSegment_097_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 270 9 9, g32p_row26_traceSegment_097_0270_0009, g32p_row26_traceSegment_097_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 252 18 18, g32p_row26_traceSegment_097_0252_0018, g32p_row26_traceSegment_097_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 216 36 36, g32p_row26_traceSegment_097_0216_0036, g32p_row26_traceSegment_097_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_097 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 144 72 72, g32p_row26_traceSegment_097_0144_0072, g32p_row26_traceSegment_097_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_097 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 0 144 144, g32p_row26_traceSegment_097_0000_0144, g32p_row26_traceSegment_097_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 288 9 9, g32p_row26_traceSegment_097_0288_0009, g32p_row26_traceSegment_097_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 306 9 9, g32p_row26_traceSegment_097_0306_0009, g32p_row26_traceSegment_097_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 288 18 18, g32p_row26_traceSegment_097_0288_0018, g32p_row26_traceSegment_097_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 324 9 9, g32p_row26_traceSegment_097_0324_0009, g32p_row26_traceSegment_097_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 342 9 9, g32p_row26_traceSegment_097_0342_0009, g32p_row26_traceSegment_097_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 324 18 18, g32p_row26_traceSegment_097_0324_0018, g32p_row26_traceSegment_097_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 288 36 36, g32p_row26_traceSegment_097_0288_0036, g32p_row26_traceSegment_097_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 360 9 9, g32p_row26_traceSegment_097_0360_0009, g32p_row26_traceSegment_097_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 378 9 9, g32p_row26_traceSegment_097_0378_0009, g32p_row26_traceSegment_097_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 360 18 18, g32p_row26_traceSegment_097_0360_0018, g32p_row26_traceSegment_097_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 396 9 9, g32p_row26_traceSegment_097_0396_0009, g32p_row26_traceSegment_097_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 414 9 9, g32p_row26_traceSegment_097_0414_0009, g32p_row26_traceSegment_097_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 396 18 18, g32p_row26_traceSegment_097_0396_0018, g32p_row26_traceSegment_097_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 360 36 36, g32p_row26_traceSegment_097_0360_0036, g32p_row26_traceSegment_097_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_097 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 288 72 72, g32p_row26_traceSegment_097_0288_0072, g32p_row26_traceSegment_097_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 432 9 9, g32p_row26_traceSegment_097_0432_0009, g32p_row26_traceSegment_097_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 450 9 9, g32p_row26_traceSegment_097_0450_0009, g32p_row26_traceSegment_097_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 432 18 18, g32p_row26_traceSegment_097_0432_0018, g32p_row26_traceSegment_097_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 468 9 9, g32p_row26_traceSegment_097_0468_0009, g32p_row26_traceSegment_097_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 486 9 9, g32p_row26_traceSegment_097_0486_0009, g32p_row26_traceSegment_097_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 468 18 18, g32p_row26_traceSegment_097_0468_0018, g32p_row26_traceSegment_097_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 432 36 36, g32p_row26_traceSegment_097_0432_0036, g32p_row26_traceSegment_097_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 504 9 9, g32p_row26_traceSegment_097_0504_0009, g32p_row26_traceSegment_097_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 522 9 9, g32p_row26_traceSegment_097_0522_0009, g32p_row26_traceSegment_097_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 504 18 18, g32p_row26_traceSegment_097_0504_0018, g32p_row26_traceSegment_097_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 540 9 9, g32p_row26_traceSegment_097_0540_0009, g32p_row26_traceSegment_097_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_097 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_097_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_097 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 558 9 9, g32p_row26_traceSegment_097_0558_0009, g32p_row26_traceSegment_097_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_097 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 540 18 18, g32p_row26_traceSegment_097_0540_0018, g32p_row26_traceSegment_097_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_097 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 504 36 36, g32p_row26_traceSegment_097_0504_0036, g32p_row26_traceSegment_097_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_097 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 432 72 72, g32p_row26_traceSegment_097_0432_0072, g32p_row26_traceSegment_097_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_097 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 288 144 144, g32p_row26_traceSegment_097_0288_0144, g32p_row26_traceSegment_097_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_097_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_097 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_097 0 288 288, g32p_row26_traceSegment_097_0000_0288, g32p_row26_traceSegment_097_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_097_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_098_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 0 9 9, g32p_row26_traceSegment_098_0000_0009, g32p_row26_traceSegment_098_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 18 9 9, g32p_row26_traceSegment_098_0018_0009, g32p_row26_traceSegment_098_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 0 18 18, g32p_row26_traceSegment_098_0000_0018, g32p_row26_traceSegment_098_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 36 9 9, g32p_row26_traceSegment_098_0036_0009, g32p_row26_traceSegment_098_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 54 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 54 9 9, g32p_row26_traceSegment_098_0054_0009, g32p_row26_traceSegment_098_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 36 18 18, g32p_row26_traceSegment_098_0036_0018, g32p_row26_traceSegment_098_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 0 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 0 36 36, g32p_row26_traceSegment_098_0000_0036, g32p_row26_traceSegment_098_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 72 9 9, g32p_row26_traceSegment_098_0072_0009, g32p_row26_traceSegment_098_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 90 9 9, g32p_row26_traceSegment_098_0090_0009, g32p_row26_traceSegment_098_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 72 18 18, g32p_row26_traceSegment_098_0072_0018, g32p_row26_traceSegment_098_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 108 9 9, g32p_row26_traceSegment_098_0108_0009, g32p_row26_traceSegment_098_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 126 9 9, g32p_row26_traceSegment_098_0126_0009, g32p_row26_traceSegment_098_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 108 18 18, g32p_row26_traceSegment_098_0108_0018, g32p_row26_traceSegment_098_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 72 36 36, g32p_row26_traceSegment_098_0072_0036, g32p_row26_traceSegment_098_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_098 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 0 72 72, g32p_row26_traceSegment_098_0000_0072, g32p_row26_traceSegment_098_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 144 9 9, g32p_row26_traceSegment_098_0144_0009, g32p_row26_traceSegment_098_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 162 9 9, g32p_row26_traceSegment_098_0162_0009, g32p_row26_traceSegment_098_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 144 18 18, g32p_row26_traceSegment_098_0144_0018, g32p_row26_traceSegment_098_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 180 9 9, g32p_row26_traceSegment_098_0180_0009, g32p_row26_traceSegment_098_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 198 9 9, g32p_row26_traceSegment_098_0198_0009, g32p_row26_traceSegment_098_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 180 18 18, g32p_row26_traceSegment_098_0180_0018, g32p_row26_traceSegment_098_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 144 36 36, g32p_row26_traceSegment_098_0144_0036, g32p_row26_traceSegment_098_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 216 9 9, g32p_row26_traceSegment_098_0216_0009, g32p_row26_traceSegment_098_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 234 9 9, g32p_row26_traceSegment_098_0234_0009, g32p_row26_traceSegment_098_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 216 18 18, g32p_row26_traceSegment_098_0216_0018, g32p_row26_traceSegment_098_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 252 9 9, g32p_row26_traceSegment_098_0252_0009, g32p_row26_traceSegment_098_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 270 9 9, g32p_row26_traceSegment_098_0270_0009, g32p_row26_traceSegment_098_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 252 18 18, g32p_row26_traceSegment_098_0252_0018, g32p_row26_traceSegment_098_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 216 36 36, g32p_row26_traceSegment_098_0216_0036, g32p_row26_traceSegment_098_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_098 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 144 72 72, g32p_row26_traceSegment_098_0144_0072, g32p_row26_traceSegment_098_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_098 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 0 144 144, g32p_row26_traceSegment_098_0000_0144, g32p_row26_traceSegment_098_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 288 9 9, g32p_row26_traceSegment_098_0288_0009, g32p_row26_traceSegment_098_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 315 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 306 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 306 9 9, g32p_row26_traceSegment_098_0306_0009, g32p_row26_traceSegment_098_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 288 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 288 18 18, g32p_row26_traceSegment_098_0288_0018, g32p_row26_traceSegment_098_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 324 9 9, g32p_row26_traceSegment_098_0324_0009, g32p_row26_traceSegment_098_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 342 9 9, g32p_row26_traceSegment_098_0342_0009, g32p_row26_traceSegment_098_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 324 18 18, g32p_row26_traceSegment_098_0324_0018, g32p_row26_traceSegment_098_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 288 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 288 36 36, g32p_row26_traceSegment_098_0288_0036, g32p_row26_traceSegment_098_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 360 9 9, g32p_row26_traceSegment_098_0360_0009, g32p_row26_traceSegment_098_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 378 9 9, g32p_row26_traceSegment_098_0378_0009, g32p_row26_traceSegment_098_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 360 18 18, g32p_row26_traceSegment_098_0360_0018, g32p_row26_traceSegment_098_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 396 9 9, g32p_row26_traceSegment_098_0396_0009, g32p_row26_traceSegment_098_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 414 9 9, g32p_row26_traceSegment_098_0414_0009, g32p_row26_traceSegment_098_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 396 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 396 18 18, g32p_row26_traceSegment_098_0396_0018, g32p_row26_traceSegment_098_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 360 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 360 36 36, g32p_row26_traceSegment_098_0360_0036, g32p_row26_traceSegment_098_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_098 288 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 288 72 72, g32p_row26_traceSegment_098_0288_0072, g32p_row26_traceSegment_098_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 432 9 9, g32p_row26_traceSegment_098_0432_0009, g32p_row26_traceSegment_098_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 450 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 450 9 9, g32p_row26_traceSegment_098_0450_0009, g32p_row26_traceSegment_098_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 432 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 432 18 18, g32p_row26_traceSegment_098_0432_0018, g32p_row26_traceSegment_098_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 468 9 9, g32p_row26_traceSegment_098_0468_0009, g32p_row26_traceSegment_098_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 486 9 9, g32p_row26_traceSegment_098_0486_0009, g32p_row26_traceSegment_098_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 468 18 18, g32p_row26_traceSegment_098_0468_0018, g32p_row26_traceSegment_098_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 432 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 432 36 36, g32p_row26_traceSegment_098_0432_0036, g32p_row26_traceSegment_098_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 504 9 9, g32p_row26_traceSegment_098_0504_0009, g32p_row26_traceSegment_098_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 522 9 9, g32p_row26_traceSegment_098_0522_0009, g32p_row26_traceSegment_098_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 504 18 18, g32p_row26_traceSegment_098_0504_0018, g32p_row26_traceSegment_098_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 540 9 9, g32p_row26_traceSegment_098_0540_0009, g32p_row26_traceSegment_098_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_098 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_098_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_098 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 558 9 9, g32p_row26_traceSegment_098_0558_0009, g32p_row26_traceSegment_098_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_098 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 540 18 18, g32p_row26_traceSegment_098_0540_0018, g32p_row26_traceSegment_098_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_098 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 504 36 36, g32p_row26_traceSegment_098_0504_0036, g32p_row26_traceSegment_098_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_098 432 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 432 72 72, g32p_row26_traceSegment_098_0432_0072, g32p_row26_traceSegment_098_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_098 288 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 288 144 144, g32p_row26_traceSegment_098_0288_0144, g32p_row26_traceSegment_098_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_098_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_098 0 576 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_098 0 288 288, g32p_row26_traceSegment_098_0000_0288, g32p_row26_traceSegment_098_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 98 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_098_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_099_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 0 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 0 9 9, g32p_row26_traceSegment_099_0000_0009, g32p_row26_traceSegment_099_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 18 9 9, g32p_row26_traceSegment_099_0018_0009, g32p_row26_traceSegment_099_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 0 18 18, g32p_row26_traceSegment_099_0000_0018, g32p_row26_traceSegment_099_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 36 9 9, g32p_row26_traceSegment_099_0036_0009, g32p_row26_traceSegment_099_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 54 9 9, g32p_row26_traceSegment_099_0054_0009, g32p_row26_traceSegment_099_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 36 18 18, g32p_row26_traceSegment_099_0036_0018, g32p_row26_traceSegment_099_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 0 36 36, g32p_row26_traceSegment_099_0000_0036, g32p_row26_traceSegment_099_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 72 9 9, g32p_row26_traceSegment_099_0072_0009, g32p_row26_traceSegment_099_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 90 9 9, g32p_row26_traceSegment_099_0090_0009, g32p_row26_traceSegment_099_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 72 18 18, g32p_row26_traceSegment_099_0072_0018, g32p_row26_traceSegment_099_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 108 9 9, g32p_row26_traceSegment_099_0108_0009, g32p_row26_traceSegment_099_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 126 9 9, g32p_row26_traceSegment_099_0126_0009, g32p_row26_traceSegment_099_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 108 18 18, g32p_row26_traceSegment_099_0108_0018, g32p_row26_traceSegment_099_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 72 36 36, g32p_row26_traceSegment_099_0072_0036, g32p_row26_traceSegment_099_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_099 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 0 72 72, g32p_row26_traceSegment_099_0000_0072, g32p_row26_traceSegment_099_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 144 9 9, g32p_row26_traceSegment_099_0144_0009, g32p_row26_traceSegment_099_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 162 9 9, g32p_row26_traceSegment_099_0162_0009, g32p_row26_traceSegment_099_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 144 18 18, g32p_row26_traceSegment_099_0144_0018, g32p_row26_traceSegment_099_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 180 9 9, g32p_row26_traceSegment_099_0180_0009, g32p_row26_traceSegment_099_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 198 9 9, g32p_row26_traceSegment_099_0198_0009, g32p_row26_traceSegment_099_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 180 18 18, g32p_row26_traceSegment_099_0180_0018, g32p_row26_traceSegment_099_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 144 36 36, g32p_row26_traceSegment_099_0144_0036, g32p_row26_traceSegment_099_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 216 9 9, g32p_row26_traceSegment_099_0216_0009, g32p_row26_traceSegment_099_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 234 9 9, g32p_row26_traceSegment_099_0234_0009, g32p_row26_traceSegment_099_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 216 18 18, g32p_row26_traceSegment_099_0216_0018, g32p_row26_traceSegment_099_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 252 9 9, g32p_row26_traceSegment_099_0252_0009, g32p_row26_traceSegment_099_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 270 9 9, g32p_row26_traceSegment_099_0270_0009, g32p_row26_traceSegment_099_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 252 18 18, g32p_row26_traceSegment_099_0252_0018, g32p_row26_traceSegment_099_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 216 36 36, g32p_row26_traceSegment_099_0216_0036, g32p_row26_traceSegment_099_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_099 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 144 72 72, g32p_row26_traceSegment_099_0144_0072, g32p_row26_traceSegment_099_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_099 0 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 0 144 144, g32p_row26_traceSegment_099_0000_0144, g32p_row26_traceSegment_099_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 288 9 9, g32p_row26_traceSegment_099_0288_0009, g32p_row26_traceSegment_099_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 306 9 9, g32p_row26_traceSegment_099_0306_0009, g32p_row26_traceSegment_099_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 288 18 18, g32p_row26_traceSegment_099_0288_0018, g32p_row26_traceSegment_099_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 324 9 9, g32p_row26_traceSegment_099_0324_0009, g32p_row26_traceSegment_099_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 342 9 9, g32p_row26_traceSegment_099_0342_0009, g32p_row26_traceSegment_099_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 324 18 18, g32p_row26_traceSegment_099_0324_0018, g32p_row26_traceSegment_099_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 288 36 36, g32p_row26_traceSegment_099_0288_0036, g32p_row26_traceSegment_099_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 360 9 9, g32p_row26_traceSegment_099_0360_0009, g32p_row26_traceSegment_099_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 378 9 9, g32p_row26_traceSegment_099_0378_0009, g32p_row26_traceSegment_099_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 360 18 18, g32p_row26_traceSegment_099_0360_0018, g32p_row26_traceSegment_099_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 396 9 9, g32p_row26_traceSegment_099_0396_0009, g32p_row26_traceSegment_099_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 414 9 9, g32p_row26_traceSegment_099_0414_0009, g32p_row26_traceSegment_099_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 396 18 18, g32p_row26_traceSegment_099_0396_0018, g32p_row26_traceSegment_099_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 360 36 36, g32p_row26_traceSegment_099_0360_0036, g32p_row26_traceSegment_099_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_099 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 288 72 72, g32p_row26_traceSegment_099_0288_0072, g32p_row26_traceSegment_099_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 432 9 9, g32p_row26_traceSegment_099_0432_0009, g32p_row26_traceSegment_099_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 450 9 9, g32p_row26_traceSegment_099_0450_0009, g32p_row26_traceSegment_099_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 432 18 18, g32p_row26_traceSegment_099_0432_0018, g32p_row26_traceSegment_099_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 468 9 9, g32p_row26_traceSegment_099_0468_0009, g32p_row26_traceSegment_099_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 486 9 9, g32p_row26_traceSegment_099_0486_0009, g32p_row26_traceSegment_099_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 468 18 18, g32p_row26_traceSegment_099_0468_0018, g32p_row26_traceSegment_099_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 432 36 36, g32p_row26_traceSegment_099_0432_0036, g32p_row26_traceSegment_099_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 504 9 9, g32p_row26_traceSegment_099_0504_0009, g32p_row26_traceSegment_099_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 522 9 9, g32p_row26_traceSegment_099_0522_0009, g32p_row26_traceSegment_099_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 504 18 18, g32p_row26_traceSegment_099_0504_0018, g32p_row26_traceSegment_099_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 540 9 9, g32p_row26_traceSegment_099_0540_0009, g32p_row26_traceSegment_099_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_099 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_099_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_099 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 558 9 9, g32p_row26_traceSegment_099_0558_0009, g32p_row26_traceSegment_099_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_099 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 540 18 18, g32p_row26_traceSegment_099_0540_0018, g32p_row26_traceSegment_099_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_099 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 504 36 36, g32p_row26_traceSegment_099_0504_0036, g32p_row26_traceSegment_099_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_099 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 432 72 72, g32p_row26_traceSegment_099_0432_0072, g32p_row26_traceSegment_099_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_099 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 288 144 144, g32p_row26_traceSegment_099_0288_0144, g32p_row26_traceSegment_099_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_099_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_099 0 576 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_099 0 288 288, g32p_row26_traceSegment_099_0000_0288, g32p_row26_traceSegment_099_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_099_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_100_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 0 9 9, g32p_row26_traceSegment_100_0000_0009, g32p_row26_traceSegment_100_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 18 9 9, g32p_row26_traceSegment_100_0018_0009, g32p_row26_traceSegment_100_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 0 18 18, g32p_row26_traceSegment_100_0000_0018, g32p_row26_traceSegment_100_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 36 9 9, g32p_row26_traceSegment_100_0036_0009, g32p_row26_traceSegment_100_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 54 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 54 9 9, g32p_row26_traceSegment_100_0054_0009, g32p_row26_traceSegment_100_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 36 18 18, g32p_row26_traceSegment_100_0036_0018, g32p_row26_traceSegment_100_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 0 36 36, g32p_row26_traceSegment_100_0000_0036, g32p_row26_traceSegment_100_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 72 9 9, g32p_row26_traceSegment_100_0072_0009, g32p_row26_traceSegment_100_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 90 9 9, g32p_row26_traceSegment_100_0090_0009, g32p_row26_traceSegment_100_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 72 18 18, g32p_row26_traceSegment_100_0072_0018, g32p_row26_traceSegment_100_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 108 9 9, g32p_row26_traceSegment_100_0108_0009, g32p_row26_traceSegment_100_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 135 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 126 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 126 9 9, g32p_row26_traceSegment_100_0126_0009, g32p_row26_traceSegment_100_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 108 18 18, g32p_row26_traceSegment_100_0108_0018, g32p_row26_traceSegment_100_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 72 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 72 36 36, g32p_row26_traceSegment_100_0072_0036, g32p_row26_traceSegment_100_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_100 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 0 72 72, g32p_row26_traceSegment_100_0000_0072, g32p_row26_traceSegment_100_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 144 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 144 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 144 9 9, g32p_row26_traceSegment_100_0144_0009, g32p_row26_traceSegment_100_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 162 9 9, g32p_row26_traceSegment_100_0162_0009, g32p_row26_traceSegment_100_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 144 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 144 18 18, g32p_row26_traceSegment_100_0144_0018, g32p_row26_traceSegment_100_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 189 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 180 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 180 9 9, g32p_row26_traceSegment_100_0180_0009, g32p_row26_traceSegment_100_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 198 9 9, g32p_row26_traceSegment_100_0198_0009, g32p_row26_traceSegment_100_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 180 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 180 18 18, g32p_row26_traceSegment_100_0180_0018, g32p_row26_traceSegment_100_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 144 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 144 36 36, g32p_row26_traceSegment_100_0144_0036, g32p_row26_traceSegment_100_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 216 9 9, g32p_row26_traceSegment_100_0216_0009, g32p_row26_traceSegment_100_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 243 9 = [1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 234 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 234 9 9, g32p_row26_traceSegment_100_0234_0009, g32p_row26_traceSegment_100_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 216 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 216 18 18, g32p_row26_traceSegment_100_0216_0018, g32p_row26_traceSegment_100_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 252 9 9, g32p_row26_traceSegment_100_0252_0009, g32p_row26_traceSegment_100_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 270 9 9, g32p_row26_traceSegment_100_0270_0009, g32p_row26_traceSegment_100_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 252 18 18, g32p_row26_traceSegment_100_0252_0018, g32p_row26_traceSegment_100_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 216 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 216 36 36, g32p_row26_traceSegment_100_0216_0036, g32p_row26_traceSegment_100_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_100 144 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 144 72 72, g32p_row26_traceSegment_100_0144_0072, g32p_row26_traceSegment_100_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_100 0 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 0 144 144, g32p_row26_traceSegment_100_0000_0144, g32p_row26_traceSegment_100_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 288 9 9, g32p_row26_traceSegment_100_0288_0009, g32p_row26_traceSegment_100_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 306 9 9, g32p_row26_traceSegment_100_0306_0009, g32p_row26_traceSegment_100_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 288 18 18, g32p_row26_traceSegment_100_0288_0018, g32p_row26_traceSegment_100_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 324 9 9, g32p_row26_traceSegment_100_0324_0009, g32p_row26_traceSegment_100_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 342 9 9, g32p_row26_traceSegment_100_0342_0009, g32p_row26_traceSegment_100_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 324 18 18, g32p_row26_traceSegment_100_0324_0018, g32p_row26_traceSegment_100_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 288 36 36, g32p_row26_traceSegment_100_0288_0036, g32p_row26_traceSegment_100_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 360 9 9, g32p_row26_traceSegment_100_0360_0009, g32p_row26_traceSegment_100_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 378 9 9, g32p_row26_traceSegment_100_0378_0009, g32p_row26_traceSegment_100_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 360 18 18, g32p_row26_traceSegment_100_0360_0018, g32p_row26_traceSegment_100_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 396 9 9, g32p_row26_traceSegment_100_0396_0009, g32p_row26_traceSegment_100_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 414 9 9, g32p_row26_traceSegment_100_0414_0009, g32p_row26_traceSegment_100_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 396 18 18, g32p_row26_traceSegment_100_0396_0018, g32p_row26_traceSegment_100_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 360 36 36, g32p_row26_traceSegment_100_0360_0036, g32p_row26_traceSegment_100_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_100 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 288 72 72, g32p_row26_traceSegment_100_0288_0072, g32p_row26_traceSegment_100_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 432 9 9, g32p_row26_traceSegment_100_0432_0009, g32p_row26_traceSegment_100_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 450 9 9, g32p_row26_traceSegment_100_0450_0009, g32p_row26_traceSegment_100_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 432 18 18, g32p_row26_traceSegment_100_0432_0018, g32p_row26_traceSegment_100_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 468 9 9, g32p_row26_traceSegment_100_0468_0009, g32p_row26_traceSegment_100_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 486 9 9, g32p_row26_traceSegment_100_0486_0009, g32p_row26_traceSegment_100_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 468 18 18, g32p_row26_traceSegment_100_0468_0018, g32p_row26_traceSegment_100_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 432 36 36, g32p_row26_traceSegment_100_0432_0036, g32p_row26_traceSegment_100_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 504 9 9, g32p_row26_traceSegment_100_0504_0009, g32p_row26_traceSegment_100_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 522 9 9, g32p_row26_traceSegment_100_0522_0009, g32p_row26_traceSegment_100_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 504 18 18, g32p_row26_traceSegment_100_0504_0018, g32p_row26_traceSegment_100_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 540 9 9, g32p_row26_traceSegment_100_0540_0009, g32p_row26_traceSegment_100_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_100 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_100_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_100 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 558 9 9, g32p_row26_traceSegment_100_0558_0009, g32p_row26_traceSegment_100_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_100 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 540 18 18, g32p_row26_traceSegment_100_0540_0018, g32p_row26_traceSegment_100_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_100 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 504 36 36, g32p_row26_traceSegment_100_0504_0036, g32p_row26_traceSegment_100_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_100 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 432 72 72, g32p_row26_traceSegment_100_0432_0072, g32p_row26_traceSegment_100_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_100 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 288 144 144, g32p_row26_traceSegment_100_0288_0144, g32p_row26_traceSegment_100_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_100_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_100 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_100 0 288 288, g32p_row26_traceSegment_100_0000_0288, g32p_row26_traceSegment_100_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 100 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_100_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row26_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row26_supplierClassifier (Fin.ofNat 576 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row26_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row26_traceSegment_101_0000_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 0 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0009_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 9 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0000_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 0 9 9, g32p_row26_traceSegment_101_0000_0009, g32p_row26_traceSegment_101_0009_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0018_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 18 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0027_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 27 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0018_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 18 9 9, g32p_row26_traceSegment_101_0018_0009, g32p_row26_traceSegment_101_0027_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0000_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 0 18 18, g32p_row26_traceSegment_101_0000_0018, g32p_row26_traceSegment_101_0018_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0036_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 36 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0045_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 45 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0036_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 36 9 9, g32p_row26_traceSegment_101_0036_0009, g32p_row26_traceSegment_101_0045_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0054_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 54 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0063_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 63 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0054_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 54 9 9, g32p_row26_traceSegment_101_0054_0009, g32p_row26_traceSegment_101_0063_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0036_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 36 18 18, g32p_row26_traceSegment_101_0036_0018, g32p_row26_traceSegment_101_0054_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0000_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 0 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 0 36 36, g32p_row26_traceSegment_101_0000_0036, g32p_row26_traceSegment_101_0036_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0072_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 72 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0081_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 81 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0072_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 72 9 9, g32p_row26_traceSegment_101_0072_0009, g32p_row26_traceSegment_101_0081_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0090_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 90 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0099_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 99 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0090_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 90 9 9, g32p_row26_traceSegment_101_0090_0009, g32p_row26_traceSegment_101_0099_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0072_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 72 18 18, g32p_row26_traceSegment_101_0072_0018, g32p_row26_traceSegment_101_0090_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0108_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 108 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0117_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 117 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0108_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 108 9 9, g32p_row26_traceSegment_101_0108_0009, g32p_row26_traceSegment_101_0117_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0126_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 126 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0135_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 135 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0126_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 126 9 9, g32p_row26_traceSegment_101_0126_0009, g32p_row26_traceSegment_101_0135_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0108_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 108 18 18, g32p_row26_traceSegment_101_0108_0018, g32p_row26_traceSegment_101_0126_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0072_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 72 36 36, g32p_row26_traceSegment_101_0072_0036, g32p_row26_traceSegment_101_0108_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0000_0144 : g32p_coeffSegment g32p_row26_traceSegment_101 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 0 72 72, g32p_row26_traceSegment_101_0000_0072, g32p_row26_traceSegment_101_0072_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0144_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 144 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0153_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 153 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0144_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 144 9 9, g32p_row26_traceSegment_101_0144_0009, g32p_row26_traceSegment_101_0153_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0162_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 162 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0171_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 171 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0162_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 162 9 9, g32p_row26_traceSegment_101_0162_0009, g32p_row26_traceSegment_101_0171_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0144_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 144 18 18, g32p_row26_traceSegment_101_0144_0018, g32p_row26_traceSegment_101_0162_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0180_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 180 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0189_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 189 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0180_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 180 9 9, g32p_row26_traceSegment_101_0180_0009, g32p_row26_traceSegment_101_0189_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0198_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 198 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0207_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 207 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0198_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 198 9 9, g32p_row26_traceSegment_101_0198_0009, g32p_row26_traceSegment_101_0207_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0180_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 180 18 18, g32p_row26_traceSegment_101_0180_0018, g32p_row26_traceSegment_101_0198_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0144_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 144 36 36, g32p_row26_traceSegment_101_0144_0036, g32p_row26_traceSegment_101_0180_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0216_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 216 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0225_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 225 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0216_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 216 9 9, g32p_row26_traceSegment_101_0216_0009, g32p_row26_traceSegment_101_0225_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0234_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 234 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0243_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 243 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0234_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 234 9 9, g32p_row26_traceSegment_101_0234_0009, g32p_row26_traceSegment_101_0243_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0216_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 216 18 18, g32p_row26_traceSegment_101_0216_0018, g32p_row26_traceSegment_101_0234_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0252_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 252 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0261_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 261 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0252_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 252 9 9, g32p_row26_traceSegment_101_0252_0009, g32p_row26_traceSegment_101_0261_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0270_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 270 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0279_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 279 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0270_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 270 9 9, g32p_row26_traceSegment_101_0270_0009, g32p_row26_traceSegment_101_0279_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0252_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 252 18 18, g32p_row26_traceSegment_101_0252_0018, g32p_row26_traceSegment_101_0270_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0216_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 216 36 36, g32p_row26_traceSegment_101_0216_0036, g32p_row26_traceSegment_101_0252_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0144_0144 : g32p_coeffSegment g32p_row26_traceSegment_101 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 144 72 72, g32p_row26_traceSegment_101_0144_0072, g32p_row26_traceSegment_101_0216_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0000_0288 : g32p_coeffSegment g32p_row26_traceSegment_101 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 0 144 144, g32p_row26_traceSegment_101_0000_0144, g32p_row26_traceSegment_101_0144_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0288_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 288 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0297_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 297 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0288_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 288 9 9, g32p_row26_traceSegment_101_0288_0009, g32p_row26_traceSegment_101_0297_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0306_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 306 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0315_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 315 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0306_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 306 9 9, g32p_row26_traceSegment_101_0306_0009, g32p_row26_traceSegment_101_0315_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0288_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 288 18 18, g32p_row26_traceSegment_101_0288_0018, g32p_row26_traceSegment_101_0306_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0324_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 324 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0333_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 333 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0324_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 324 9 9, g32p_row26_traceSegment_101_0324_0009, g32p_row26_traceSegment_101_0333_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0342_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 342 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0351_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 351 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0342_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 342 9 9, g32p_row26_traceSegment_101_0342_0009, g32p_row26_traceSegment_101_0351_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0324_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 324 18 18, g32p_row26_traceSegment_101_0324_0018, g32p_row26_traceSegment_101_0342_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0288_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 288 36 36, g32p_row26_traceSegment_101_0288_0036, g32p_row26_traceSegment_101_0324_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0360_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 360 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0369_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 369 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0360_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 360 9 9, g32p_row26_traceSegment_101_0360_0009, g32p_row26_traceSegment_101_0369_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0378_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 378 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0387_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 387 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0378_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 378 9 9, g32p_row26_traceSegment_101_0378_0009, g32p_row26_traceSegment_101_0387_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0360_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 360 18 18, g32p_row26_traceSegment_101_0360_0018, g32p_row26_traceSegment_101_0378_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0396_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 396 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0405_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 405 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0396_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 396 9 9, g32p_row26_traceSegment_101_0396_0009, g32p_row26_traceSegment_101_0405_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0414_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 414 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0423_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 423 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0414_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 414 9 9, g32p_row26_traceSegment_101_0414_0009, g32p_row26_traceSegment_101_0423_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0396_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 396 18 18, g32p_row26_traceSegment_101_0396_0018, g32p_row26_traceSegment_101_0414_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0360_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 360 36 36, g32p_row26_traceSegment_101_0360_0036, g32p_row26_traceSegment_101_0396_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0288_0144 : g32p_coeffSegment g32p_row26_traceSegment_101 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 288 72 72, g32p_row26_traceSegment_101_0288_0072, g32p_row26_traceSegment_101_0360_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0432_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 432 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0441_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 441 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0432_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 432 9 9, g32p_row26_traceSegment_101_0432_0009, g32p_row26_traceSegment_101_0441_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0450_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 450 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0459_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 459 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0450_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 450 9 9, g32p_row26_traceSegment_101_0450_0009, g32p_row26_traceSegment_101_0459_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0432_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 432 18 18, g32p_row26_traceSegment_101_0432_0018, g32p_row26_traceSegment_101_0450_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0468_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 468 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0477_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 477 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0468_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 468 9 9, g32p_row26_traceSegment_101_0468_0009, g32p_row26_traceSegment_101_0477_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0486_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 486 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0495_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 495 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0486_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 486 9 9, g32p_row26_traceSegment_101_0486_0009, g32p_row26_traceSegment_101_0495_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0468_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 468 18 18, g32p_row26_traceSegment_101_0468_0018, g32p_row26_traceSegment_101_0486_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0432_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 432 36 36, g32p_row26_traceSegment_101_0432_0036, g32p_row26_traceSegment_101_0468_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0504_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 504 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0513_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 513 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0504_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 504 9 9, g32p_row26_traceSegment_101_0504_0009, g32p_row26_traceSegment_101_0513_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0522_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 522 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0531_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 531 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0522_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 522 9 9, g32p_row26_traceSegment_101_0522_0009, g32p_row26_traceSegment_101_0531_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0504_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 504 18 18, g32p_row26_traceSegment_101_0504_0018, g32p_row26_traceSegment_101_0522_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0540_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 540 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0549_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 549 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0540_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 540 9 9, g32p_row26_traceSegment_101_0540_0009, g32p_row26_traceSegment_101_0549_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0558_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 558 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0567_0009 : g32p_coeffSegment g32p_row26_traceSegment_101 567 9 = [] := by
  decide +kernel

private theorem g32p_row26_traceSegment_101_0558_0018 : g32p_coeffSegment g32p_row26_traceSegment_101 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 558 9 9, g32p_row26_traceSegment_101_0558_0009, g32p_row26_traceSegment_101_0567_0009]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0540_0036 : g32p_coeffSegment g32p_row26_traceSegment_101 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 540 18 18, g32p_row26_traceSegment_101_0540_0018, g32p_row26_traceSegment_101_0558_0018]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0504_0072 : g32p_coeffSegment g32p_row26_traceSegment_101 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 504 36 36, g32p_row26_traceSegment_101_0504_0036, g32p_row26_traceSegment_101_0540_0036]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0432_0144 : g32p_coeffSegment g32p_row26_traceSegment_101 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 432 72 72, g32p_row26_traceSegment_101_0432_0072, g32p_row26_traceSegment_101_0504_0072]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0288_0288 : g32p_coeffSegment g32p_row26_traceSegment_101 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 288 144 144, g32p_row26_traceSegment_101_0288_0144, g32p_row26_traceSegment_101_0432_0144]
  decide +kernel

private theorem g32p_row26_traceSegment_101_0000_0576 : g32p_coeffSegment g32p_row26_traceSegment_101 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row26_traceSegment_101 0 288 288, g32p_row26_traceSegment_101_0000_0288, g32p_row26_traceSegment_101_0288_0288]
  decide +kernel

theorem g32p_row26_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row26_traceSegment_101_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row26_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 96) (g32p_literalTraceValue 25 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_096]
  decide +kernel

theorem g32p_row26_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 97) (g32p_literalTraceValue 25 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_097]
  decide +kernel

theorem g32p_row26_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 98) (g32p_literalTraceValue 25 98)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row26_traceCoefficients_098]
  decide +kernel

theorem g32p_row26_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 99) (g32p_literalTraceValue 25 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_099]
  decide +kernel

theorem g32p_row26_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 100) (g32p_literalTraceValue 25 100)
      [1, -1, 1] [] = true := by
  rw [g32p_row26_traceCoefficients_100]
  decide +kernel

theorem g32p_row26_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) 101) (g32p_literalTraceValue 25 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row26_traceCoefficients_101]
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

def g32p_row26_generatorIndex : Fin 8 → Fin 408 :=
  ![25, 76, 127, 178, 254, 255, 356, 357]

theorem g32p_row26_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup20_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 25 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 25 g32p_row26_supplierClass
    g32p_row26_supplierClass_isConj g32p_supplierGroup20_support g32p_row26_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row26_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup20_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row26_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 25 c false (g32p_row26_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 25 c true (g32p_row26_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 25 c false (g32p_row26_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 25 c true (g32p_row26_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 25 c false (g32p_row26_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 25 c false (g32p_row26_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 25 c true (g32p_row26_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 25 c true (g32p_row26_coinduced_zero c hc true) 3

theorem g32p_row26_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row26_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row26_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup20_support) :
    g32p_literalTraceValue (g32p_row26_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup20_support →
    g32p_literalTraceValue (g32p_row26_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row26_zeroTrace_block_00 r k
  · exact g32p_row26_zeroTrace_block_01 r k
  · exact g32p_row26_zeroTrace_block_02 r k
  · exact g32p_row26_zeroTrace_block_03 r k
  · exact g32p_row26_zeroTrace_block_04 r k
  · exact g32p_row26_zeroTrace_block_05 r k
  · exact g32p_row26_zeroTrace_block_06 r k

theorem g32p_row26_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup20_support) :
    (g32p_recordedInductionGenerators (g32p_row26_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row26_generatorIndex k) c) := by
  rw [g32p_row26_recordedGenerator_zero c hc k, g32p_row26_zeroTrace_arithmetic c k hc]
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

def g32p_row26_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [15552, 15552, 15552] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else [1152, 1152]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [-576, 576, 576] else [1728, 1728, 1728])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 6912, 6912] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else [1152, 1152]))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [0, 0, 1152, 1152])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [1728, 1728, 1728] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [1152, 1152])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [1152, 2304, 2304] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [-3456, 3456, 3456] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [0, 0, 1152, 1152] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else [-576, 576, 576]) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [0, 0, 1152, 1152] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [1152, 1152] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [0, 0, 1152, 1152] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [1152, 1152] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [0, 0, 1152, 1152] else (if i.val < 65 then [] else [3456, 3456, 3456])) else (if i.val < 67 then [] else (if i.val < 68 then [15552, 15552, 15552] else []))) else (if i.val < 72 then (if i.val < 70 then [6912, 6912] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [-576, 576, 576] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [1728, 1728, 1728] else (if i.val < 81 then [-576, 576, 576] else [1728, 1728, 1728]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [0, 0, 1152, 1152] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [1152, 2304, 2304] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [1152, 1152]))) else (if i.val < 98 then (if i.val < 96 then [15552, 15552, 15552] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [15552, 15552, 15552] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row26_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup20_support) :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) c) (g32p_literalTraceValue 25 c)
      [1, -1, 1] (g32p_row26_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row26_tracePolynomial_000
  · exact g32p_row26_tracePolynomial_001
  · exact g32p_row26_tracePolynomial_002
  · exact g32p_row26_tracePolynomial_003
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_007
  · exact g32p_row26_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_017
  · exact g32p_row26_tracePolynomial_018
  · exact g32p_row26_tracePolynomial_019
  · exact g32p_row26_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_027
  · exact g32p_row26_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_044
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_051
  · exact g32p_row26_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_055
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_058
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_063
  · exact g32p_row26_tracePolynomial_064
  · exact g32p_row26_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_076
  · exact g32p_row26_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_079
  · exact g32p_row26_tracePolynomial_080
  · exact g32p_row26_tracePolynomial_081
  · exact g32p_row26_tracePolynomial_082
  · exact g32p_row26_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_085
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_087
  · exact g32p_row26_tracePolynomial_088
  · exact g32p_row26_tracePolynomial_089
  · exact g32p_row26_tracePolynomial_090
  · exact g32p_row26_tracePolynomial_091
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row26_tracePolynomial_093
  · exact g32p_row26_tracePolynomial_094
  · exact g32p_row26_tracePolynomial_095
  · exact g32p_row26_tracePolynomial_096
  · exact g32p_row26_tracePolynomial_097
  · exact g32p_row26_tracePolynomial_098
  · exact g32p_row26_tracePolynomial_099
  · exact g32p_row26_tracePolynomial_100
  · exact g32p_row26_tracePolynomial_101

theorem g32p_row26_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 25 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 25 c) := by
  by_cases hc : c ∈ g32p_supplierGroup20_support
  · have hclass (j : Fin 576) :
        IsConj (g32p_literalRepresentative c) (g32p_row26_groupEquiv j : g32p_G) ↔
          g32p_row26_supplierClassifier j = c := by
      simpa only [g32p_row26_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row26_supplierClass_iff (g32p_row26_groupEquiv j) c
    have hχ (j : Fin 576) :
        (g32p_recordedSupplierCharacters 25 (g32p_row26_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row26_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 25 (show (g32p_recordedSuppliers 25).H from g32p_row26_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row26_characterValues (g32p_row26_groupEquiv.symm (g32p_row26_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 25).H (g32p_recordedSupplierCharacters 25)
      (g32p_literalRepresentative c) g32p_row26_groupEquiv g32p_row26_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row26_characterValues j)).val) c 6 576
      (g32p_literalCentralizer c) (g32p_literalTraceValue 25 c) [1, -1, 1]
      (g32p_row26_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row26_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 25)))
      (g32p_row26_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row26_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end
