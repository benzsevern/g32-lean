import HodgeLean.Foundations.Program.G32PropFourSixPacked0425
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0428
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0426
import HodgeLean.Foundations.Program.G32PropFourSixPacked0427
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0414
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row42_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row42_supplierClassifier (Fin.ofNat 576 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row42_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row42_traceSegment_100_0000_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 0 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0009_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 9 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0000_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 0 9 9, g32p_row42_traceSegment_100_0000_0009, g32p_row42_traceSegment_100_0009_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0018_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 18 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0027_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 27 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0018_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 18 9 9, g32p_row42_traceSegment_100_0018_0009, g32p_row42_traceSegment_100_0027_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0000_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 0 18 18, g32p_row42_traceSegment_100_0000_0018, g32p_row42_traceSegment_100_0018_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0036_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 36 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0045_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 45 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0036_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 36 9 9, g32p_row42_traceSegment_100_0036_0009, g32p_row42_traceSegment_100_0045_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0054_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 54 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0063_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 63 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0054_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 54 9 9, g32p_row42_traceSegment_100_0054_0009, g32p_row42_traceSegment_100_0063_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0036_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 36 18 18, g32p_row42_traceSegment_100_0036_0018, g32p_row42_traceSegment_100_0054_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0000_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 0 36 36, g32p_row42_traceSegment_100_0000_0036, g32p_row42_traceSegment_100_0036_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0072_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 72 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0081_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 81 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0072_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 72 9 9, g32p_row42_traceSegment_100_0072_0009, g32p_row42_traceSegment_100_0081_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0090_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 90 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0099_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 99 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0090_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 90 9 9, g32p_row42_traceSegment_100_0090_0009, g32p_row42_traceSegment_100_0099_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0072_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 72 18 18, g32p_row42_traceSegment_100_0072_0018, g32p_row42_traceSegment_100_0090_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0108_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 108 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0117_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 117 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0108_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 108 9 9, g32p_row42_traceSegment_100_0108_0009, g32p_row42_traceSegment_100_0117_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0126_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 126 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0135_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 135 9 = [1] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0126_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 126 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 126 9 9, g32p_row42_traceSegment_100_0126_0009, g32p_row42_traceSegment_100_0135_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0108_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 108 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 108 18 18, g32p_row42_traceSegment_100_0108_0018, g32p_row42_traceSegment_100_0126_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0072_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 72 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 72 36 36, g32p_row42_traceSegment_100_0072_0036, g32p_row42_traceSegment_100_0108_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0000_0144 : g32p_coeffSegment g32p_row42_traceSegment_100 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 0 72 72, g32p_row42_traceSegment_100_0000_0072, g32p_row42_traceSegment_100_0072_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0144_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 144 9 = [1] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0153_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 153 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0144_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 144 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 144 9 9, g32p_row42_traceSegment_100_0144_0009, g32p_row42_traceSegment_100_0153_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0162_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 162 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0171_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 171 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0162_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 162 9 9, g32p_row42_traceSegment_100_0162_0009, g32p_row42_traceSegment_100_0171_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0144_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 144 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 144 18 18, g32p_row42_traceSegment_100_0144_0018, g32p_row42_traceSegment_100_0162_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0180_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 180 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0189_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 189 9 = [1] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0180_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 180 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 180 9 9, g32p_row42_traceSegment_100_0180_0009, g32p_row42_traceSegment_100_0189_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0198_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 198 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0207_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 207 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0198_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 198 9 9, g32p_row42_traceSegment_100_0198_0009, g32p_row42_traceSegment_100_0207_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0180_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 180 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 180 18 18, g32p_row42_traceSegment_100_0180_0018, g32p_row42_traceSegment_100_0198_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0144_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 144 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 144 36 36, g32p_row42_traceSegment_100_0144_0036, g32p_row42_traceSegment_100_0180_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0216_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 216 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0225_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 225 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0216_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 216 9 9, g32p_row42_traceSegment_100_0216_0009, g32p_row42_traceSegment_100_0225_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0234_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 234 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0243_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 243 9 = [1] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0234_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 234 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 234 9 9, g32p_row42_traceSegment_100_0234_0009, g32p_row42_traceSegment_100_0243_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0216_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 216 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 216 18 18, g32p_row42_traceSegment_100_0216_0018, g32p_row42_traceSegment_100_0234_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0252_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 252 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0261_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 261 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0252_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 252 9 9, g32p_row42_traceSegment_100_0252_0009, g32p_row42_traceSegment_100_0261_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0270_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 270 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0279_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 279 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0270_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 270 9 9, g32p_row42_traceSegment_100_0270_0009, g32p_row42_traceSegment_100_0279_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0252_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 252 18 18, g32p_row42_traceSegment_100_0252_0018, g32p_row42_traceSegment_100_0270_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0216_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 216 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 216 36 36, g32p_row42_traceSegment_100_0216_0036, g32p_row42_traceSegment_100_0252_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0144_0144 : g32p_coeffSegment g32p_row42_traceSegment_100 144 144 = [3] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 144 72 72, g32p_row42_traceSegment_100_0144_0072, g32p_row42_traceSegment_100_0216_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0000_0288 : g32p_coeffSegment g32p_row42_traceSegment_100 0 288 = [4] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 0 144 144, g32p_row42_traceSegment_100_0000_0144, g32p_row42_traceSegment_100_0144_0144]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0288_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 288 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0297_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 297 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0288_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 288 9 9, g32p_row42_traceSegment_100_0288_0009, g32p_row42_traceSegment_100_0297_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0306_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 306 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0315_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 315 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0306_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 306 9 9, g32p_row42_traceSegment_100_0306_0009, g32p_row42_traceSegment_100_0315_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0288_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 288 18 18, g32p_row42_traceSegment_100_0288_0018, g32p_row42_traceSegment_100_0306_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0324_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 324 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0333_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 333 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0324_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 324 9 9, g32p_row42_traceSegment_100_0324_0009, g32p_row42_traceSegment_100_0333_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0342_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 342 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0351_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 351 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0342_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 342 9 9, g32p_row42_traceSegment_100_0342_0009, g32p_row42_traceSegment_100_0351_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0324_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 324 18 18, g32p_row42_traceSegment_100_0324_0018, g32p_row42_traceSegment_100_0342_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0288_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 288 36 36, g32p_row42_traceSegment_100_0288_0036, g32p_row42_traceSegment_100_0324_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0360_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 360 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0369_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 369 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0360_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 360 9 9, g32p_row42_traceSegment_100_0360_0009, g32p_row42_traceSegment_100_0369_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0378_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 378 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0387_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 387 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0378_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 378 9 9, g32p_row42_traceSegment_100_0378_0009, g32p_row42_traceSegment_100_0387_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0360_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 360 18 18, g32p_row42_traceSegment_100_0360_0018, g32p_row42_traceSegment_100_0378_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0396_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 396 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0405_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 405 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0396_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 396 9 9, g32p_row42_traceSegment_100_0396_0009, g32p_row42_traceSegment_100_0405_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0414_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 414 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0423_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 423 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0414_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 414 9 9, g32p_row42_traceSegment_100_0414_0009, g32p_row42_traceSegment_100_0423_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0396_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 396 18 18, g32p_row42_traceSegment_100_0396_0018, g32p_row42_traceSegment_100_0414_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0360_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 360 36 36, g32p_row42_traceSegment_100_0360_0036, g32p_row42_traceSegment_100_0396_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0288_0144 : g32p_coeffSegment g32p_row42_traceSegment_100 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 288 72 72, g32p_row42_traceSegment_100_0288_0072, g32p_row42_traceSegment_100_0360_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0432_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 432 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0441_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 441 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0432_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 432 9 9, g32p_row42_traceSegment_100_0432_0009, g32p_row42_traceSegment_100_0441_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0450_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 450 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0459_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 459 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0450_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 450 9 9, g32p_row42_traceSegment_100_0450_0009, g32p_row42_traceSegment_100_0459_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0432_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 432 18 18, g32p_row42_traceSegment_100_0432_0018, g32p_row42_traceSegment_100_0450_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0468_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 468 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0477_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 477 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0468_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 468 9 9, g32p_row42_traceSegment_100_0468_0009, g32p_row42_traceSegment_100_0477_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0486_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 486 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0495_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 495 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0486_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 486 9 9, g32p_row42_traceSegment_100_0486_0009, g32p_row42_traceSegment_100_0495_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0468_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 468 18 18, g32p_row42_traceSegment_100_0468_0018, g32p_row42_traceSegment_100_0486_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0432_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 432 36 36, g32p_row42_traceSegment_100_0432_0036, g32p_row42_traceSegment_100_0468_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0504_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 504 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0513_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 513 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0504_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 504 9 9, g32p_row42_traceSegment_100_0504_0009, g32p_row42_traceSegment_100_0513_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0522_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 522 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0531_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 531 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0522_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 522 9 9, g32p_row42_traceSegment_100_0522_0009, g32p_row42_traceSegment_100_0531_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0504_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 504 18 18, g32p_row42_traceSegment_100_0504_0018, g32p_row42_traceSegment_100_0522_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0540_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 540 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0549_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 549 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0540_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 540 9 9, g32p_row42_traceSegment_100_0540_0009, g32p_row42_traceSegment_100_0549_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0558_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 558 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0567_0009 : g32p_coeffSegment g32p_row42_traceSegment_100 567 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_100_0558_0018 : g32p_coeffSegment g32p_row42_traceSegment_100 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 558 9 9, g32p_row42_traceSegment_100_0558_0009, g32p_row42_traceSegment_100_0567_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0540_0036 : g32p_coeffSegment g32p_row42_traceSegment_100 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 540 18 18, g32p_row42_traceSegment_100_0540_0018, g32p_row42_traceSegment_100_0558_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0504_0072 : g32p_coeffSegment g32p_row42_traceSegment_100 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 504 36 36, g32p_row42_traceSegment_100_0504_0036, g32p_row42_traceSegment_100_0540_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0432_0144 : g32p_coeffSegment g32p_row42_traceSegment_100 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 432 72 72, g32p_row42_traceSegment_100_0432_0072, g32p_row42_traceSegment_100_0504_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0288_0288 : g32p_coeffSegment g32p_row42_traceSegment_100 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 288 144 144, g32p_row42_traceSegment_100_0288_0144, g32p_row42_traceSegment_100_0432_0144]
  decide +kernel

private theorem g32p_row42_traceSegment_100_0000_0576 : g32p_coeffSegment g32p_row42_traceSegment_100 0 576 = [4] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_100 0 288 288, g32p_row42_traceSegment_100_0000_0288, g32p_row42_traceSegment_100_0288_0288]
  decide +kernel

theorem g32p_row42_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 100 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row42_traceSegment_100_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row42_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row42_supplierClassifier (Fin.ofNat 576 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row42_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row42_traceSegment_101_0000_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 0 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0009_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 9 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0000_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 0 9 9, g32p_row42_traceSegment_101_0000_0009, g32p_row42_traceSegment_101_0009_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0018_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 18 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0027_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 27 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0018_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 18 9 9, g32p_row42_traceSegment_101_0018_0009, g32p_row42_traceSegment_101_0027_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0000_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 0 18 18, g32p_row42_traceSegment_101_0000_0018, g32p_row42_traceSegment_101_0018_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0036_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 36 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0045_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 45 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0036_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 36 9 9, g32p_row42_traceSegment_101_0036_0009, g32p_row42_traceSegment_101_0045_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0054_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 54 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0063_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 63 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0054_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 54 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 54 9 9, g32p_row42_traceSegment_101_0054_0009, g32p_row42_traceSegment_101_0063_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0036_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 36 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 36 18 18, g32p_row42_traceSegment_101_0036_0018, g32p_row42_traceSegment_101_0054_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0000_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 0 36 36, g32p_row42_traceSegment_101_0000_0036, g32p_row42_traceSegment_101_0036_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0072_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 72 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0081_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 81 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0072_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 72 9 9, g32p_row42_traceSegment_101_0072_0009, g32p_row42_traceSegment_101_0081_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0090_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 90 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0099_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 99 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0090_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 90 9 9, g32p_row42_traceSegment_101_0090_0009, g32p_row42_traceSegment_101_0099_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0072_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 72 18 18, g32p_row42_traceSegment_101_0072_0018, g32p_row42_traceSegment_101_0090_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0108_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 108 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0117_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 117 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0108_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 108 9 9, g32p_row42_traceSegment_101_0108_0009, g32p_row42_traceSegment_101_0117_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0126_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 126 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0135_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 135 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0126_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 126 9 9, g32p_row42_traceSegment_101_0126_0009, g32p_row42_traceSegment_101_0135_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0108_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 108 18 18, g32p_row42_traceSegment_101_0108_0018, g32p_row42_traceSegment_101_0126_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0072_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 72 36 36, g32p_row42_traceSegment_101_0072_0036, g32p_row42_traceSegment_101_0108_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0000_0144 : g32p_coeffSegment g32p_row42_traceSegment_101 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 0 72 72, g32p_row42_traceSegment_101_0000_0072, g32p_row42_traceSegment_101_0072_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0144_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 144 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0153_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 153 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0144_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 144 9 9, g32p_row42_traceSegment_101_0144_0009, g32p_row42_traceSegment_101_0153_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0162_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 162 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0171_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 171 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0162_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 162 9 9, g32p_row42_traceSegment_101_0162_0009, g32p_row42_traceSegment_101_0171_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0144_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 144 18 18, g32p_row42_traceSegment_101_0144_0018, g32p_row42_traceSegment_101_0162_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0180_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 180 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0189_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 189 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0180_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 180 9 9, g32p_row42_traceSegment_101_0180_0009, g32p_row42_traceSegment_101_0189_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0198_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 198 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0207_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 207 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0198_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 198 9 9, g32p_row42_traceSegment_101_0198_0009, g32p_row42_traceSegment_101_0207_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0180_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 180 18 18, g32p_row42_traceSegment_101_0180_0018, g32p_row42_traceSegment_101_0198_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0144_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 144 36 36, g32p_row42_traceSegment_101_0144_0036, g32p_row42_traceSegment_101_0180_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0216_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 216 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0225_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 225 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0216_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 216 9 9, g32p_row42_traceSegment_101_0216_0009, g32p_row42_traceSegment_101_0225_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0234_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 234 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0243_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 243 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0234_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 234 9 9, g32p_row42_traceSegment_101_0234_0009, g32p_row42_traceSegment_101_0243_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0216_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 216 18 18, g32p_row42_traceSegment_101_0216_0018, g32p_row42_traceSegment_101_0234_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0252_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 252 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0261_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 261 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0252_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 252 9 9, g32p_row42_traceSegment_101_0252_0009, g32p_row42_traceSegment_101_0261_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0270_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 270 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0279_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 279 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0270_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 270 9 9, g32p_row42_traceSegment_101_0270_0009, g32p_row42_traceSegment_101_0279_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0252_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 252 18 18, g32p_row42_traceSegment_101_0252_0018, g32p_row42_traceSegment_101_0270_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0216_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 216 36 36, g32p_row42_traceSegment_101_0216_0036, g32p_row42_traceSegment_101_0252_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0144_0144 : g32p_coeffSegment g32p_row42_traceSegment_101 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 144 72 72, g32p_row42_traceSegment_101_0144_0072, g32p_row42_traceSegment_101_0216_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0000_0288 : g32p_coeffSegment g32p_row42_traceSegment_101 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 0 144 144, g32p_row42_traceSegment_101_0000_0144, g32p_row42_traceSegment_101_0144_0144]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0288_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 288 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0297_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 297 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0288_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 288 9 9, g32p_row42_traceSegment_101_0288_0009, g32p_row42_traceSegment_101_0297_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0306_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 306 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0315_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 315 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0306_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 306 9 9, g32p_row42_traceSegment_101_0306_0009, g32p_row42_traceSegment_101_0315_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0288_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 288 18 18, g32p_row42_traceSegment_101_0288_0018, g32p_row42_traceSegment_101_0306_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0324_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 324 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0333_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 333 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0324_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 324 9 9, g32p_row42_traceSegment_101_0324_0009, g32p_row42_traceSegment_101_0333_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0342_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 342 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0351_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 351 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0342_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 342 9 9, g32p_row42_traceSegment_101_0342_0009, g32p_row42_traceSegment_101_0351_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0324_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 324 18 18, g32p_row42_traceSegment_101_0324_0018, g32p_row42_traceSegment_101_0342_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0288_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 288 36 36, g32p_row42_traceSegment_101_0288_0036, g32p_row42_traceSegment_101_0324_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0360_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 360 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0369_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 369 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0360_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 360 9 9, g32p_row42_traceSegment_101_0360_0009, g32p_row42_traceSegment_101_0369_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0378_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 378 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0387_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 387 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0378_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 378 9 9, g32p_row42_traceSegment_101_0378_0009, g32p_row42_traceSegment_101_0387_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0360_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 360 18 18, g32p_row42_traceSegment_101_0360_0018, g32p_row42_traceSegment_101_0378_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0396_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 396 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0405_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 405 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0396_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 396 9 9, g32p_row42_traceSegment_101_0396_0009, g32p_row42_traceSegment_101_0405_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0414_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 414 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0423_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 423 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0414_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 414 9 9, g32p_row42_traceSegment_101_0414_0009, g32p_row42_traceSegment_101_0423_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0396_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 396 18 18, g32p_row42_traceSegment_101_0396_0018, g32p_row42_traceSegment_101_0414_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0360_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 360 36 36, g32p_row42_traceSegment_101_0360_0036, g32p_row42_traceSegment_101_0396_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0288_0144 : g32p_coeffSegment g32p_row42_traceSegment_101 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 288 72 72, g32p_row42_traceSegment_101_0288_0072, g32p_row42_traceSegment_101_0360_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0432_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 432 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0441_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 441 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0432_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 432 9 9, g32p_row42_traceSegment_101_0432_0009, g32p_row42_traceSegment_101_0441_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0450_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 450 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0459_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 459 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0450_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 450 9 9, g32p_row42_traceSegment_101_0450_0009, g32p_row42_traceSegment_101_0459_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0432_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 432 18 18, g32p_row42_traceSegment_101_0432_0018, g32p_row42_traceSegment_101_0450_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0468_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 468 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0477_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 477 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0468_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 468 9 9, g32p_row42_traceSegment_101_0468_0009, g32p_row42_traceSegment_101_0477_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0486_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 486 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0495_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 495 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0486_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 486 9 9, g32p_row42_traceSegment_101_0486_0009, g32p_row42_traceSegment_101_0495_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0468_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 468 18 18, g32p_row42_traceSegment_101_0468_0018, g32p_row42_traceSegment_101_0486_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0432_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 432 36 36, g32p_row42_traceSegment_101_0432_0036, g32p_row42_traceSegment_101_0468_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0504_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 504 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0513_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 513 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0504_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 504 9 9, g32p_row42_traceSegment_101_0504_0009, g32p_row42_traceSegment_101_0513_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0522_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 522 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0531_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 531 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0522_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 522 9 9, g32p_row42_traceSegment_101_0522_0009, g32p_row42_traceSegment_101_0531_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0504_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 504 18 18, g32p_row42_traceSegment_101_0504_0018, g32p_row42_traceSegment_101_0522_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0540_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 540 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0549_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 549 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0540_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 540 9 9, g32p_row42_traceSegment_101_0540_0009, g32p_row42_traceSegment_101_0549_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0558_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 558 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0567_0009 : g32p_coeffSegment g32p_row42_traceSegment_101 567 9 = [] := by
  decide +kernel

private theorem g32p_row42_traceSegment_101_0558_0018 : g32p_coeffSegment g32p_row42_traceSegment_101 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 558 9 9, g32p_row42_traceSegment_101_0558_0009, g32p_row42_traceSegment_101_0567_0009]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0540_0036 : g32p_coeffSegment g32p_row42_traceSegment_101 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 540 18 18, g32p_row42_traceSegment_101_0540_0018, g32p_row42_traceSegment_101_0558_0018]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0504_0072 : g32p_coeffSegment g32p_row42_traceSegment_101 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 504 36 36, g32p_row42_traceSegment_101_0504_0036, g32p_row42_traceSegment_101_0540_0036]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0432_0144 : g32p_coeffSegment g32p_row42_traceSegment_101 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 432 72 72, g32p_row42_traceSegment_101_0432_0072, g32p_row42_traceSegment_101_0504_0072]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0288_0288 : g32p_coeffSegment g32p_row42_traceSegment_101 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 288 144 144, g32p_row42_traceSegment_101_0288_0144, g32p_row42_traceSegment_101_0432_0144]
  decide +kernel

private theorem g32p_row42_traceSegment_101_0000_0576 : g32p_coeffSegment g32p_row42_traceSegment_101 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row42_traceSegment_101 0 288 288, g32p_row42_traceSegment_101_0000_0288, g32p_row42_traceSegment_101_0288_0288]
  decide +kernel

theorem g32p_row42_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 101 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row42_traceSegment_101_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row42_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 96) (g32p_literalTraceValue 41 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row42_traceCoefficients_096]
  decide +kernel

theorem g32p_row42_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 97) (g32p_literalTraceValue 41 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row42_traceCoefficients_097]
  decide +kernel

theorem g32p_row42_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 98) (g32p_literalTraceValue 41 98)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row42_traceCoefficients_098]
  decide +kernel

theorem g32p_row42_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 99) (g32p_literalTraceValue 41 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row42_traceCoefficients_099]
  decide +kernel

theorem g32p_row42_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 100) (g32p_literalTraceValue 41 100)
      [1, 1, 1] [] = true := by
  rw [g32p_row42_traceCoefficients_100]
  decide +kernel

theorem g32p_row42_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) 101) (g32p_literalTraceValue 41 101)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row42_traceCoefficients_101]
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

def g32p_row42_generatorIndex : Fin 8 → Fin 408 :=
  ![41, 92, 143, 194, 286, 287, 388, 389]

theorem g32p_row42_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup20_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 41 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 41 g32p_row42_supplierClass
    g32p_row42_supplierClass_isConj g32p_supplierGroup20_support g32p_row42_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row42_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup20_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row42_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 41 c false (g32p_row42_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 41 c true (g32p_row42_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 41 c false (g32p_row42_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 41 c true (g32p_row42_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 41 c false (g32p_row42_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 41 c false (g32p_row42_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 41 c true (g32p_row42_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 41 c true (g32p_row42_coinduced_zero c hc true) 3

theorem g32p_row42_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup20_support →
      g32p_literalTraceValue (g32p_row42_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row42_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup20_support) :
    g32p_literalTraceValue (g32p_row42_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup20_support →
    g32p_literalTraceValue (g32p_row42_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row42_zeroTrace_block_00 r k
  · exact g32p_row42_zeroTrace_block_01 r k
  · exact g32p_row42_zeroTrace_block_02 r k
  · exact g32p_row42_zeroTrace_block_03 r k
  · exact g32p_row42_zeroTrace_block_04 r k
  · exact g32p_row42_zeroTrace_block_05 r k
  · exact g32p_row42_zeroTrace_block_06 r k

theorem g32p_row42_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup20_support) :
    (g32p_recordedInductionGenerators (g32p_row42_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row42_generatorIndex k) c) := by
  rw [g32p_row42_recordedGenerator_zero c hc k, g32p_row42_zeroTrace_arithmetic c k hc]
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

def g32p_row42_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [15552] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [1728] else [1728])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [1728] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [3456] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [10368] else []) else (if i.val < 37 then [] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else [1728]) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [3456])) else (if i.val < 67 then [] else (if i.val < 68 then [15552] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [1728] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [1728] else (if i.val < 81 then [1728] else [1728]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [3456] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [15552] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [15552] else []) else (if i.val < 101 then [] else [155520])))))))

theorem g32p_row42_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup20_support) :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) c) (g32p_literalTraceValue 41 c)
      [1, 1, 1] (g32p_row42_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row42_tracePolynomial_000
  · exact g32p_row42_tracePolynomial_001
  · exact g32p_row42_tracePolynomial_002
  · exact g32p_row42_tracePolynomial_003
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_007
  · exact g32p_row42_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_017
  · exact g32p_row42_tracePolynomial_018
  · exact g32p_row42_tracePolynomial_019
  · exact g32p_row42_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_027
  · exact g32p_row42_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_044
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_051
  · exact g32p_row42_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_055
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_058
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_063
  · exact g32p_row42_tracePolynomial_064
  · exact g32p_row42_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_076
  · exact g32p_row42_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_079
  · exact g32p_row42_tracePolynomial_080
  · exact g32p_row42_tracePolynomial_081
  · exact g32p_row42_tracePolynomial_082
  · exact g32p_row42_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_085
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_087
  · exact g32p_row42_tracePolynomial_088
  · exact g32p_row42_tracePolynomial_089
  · exact g32p_row42_tracePolynomial_090
  · exact g32p_row42_tracePolynomial_091
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup20_support) hc)
  · exact g32p_row42_tracePolynomial_093
  · exact g32p_row42_tracePolynomial_094
  · exact g32p_row42_tracePolynomial_095
  · exact g32p_row42_tracePolynomial_096
  · exact g32p_row42_tracePolynomial_097
  · exact g32p_row42_tracePolynomial_098
  · exact g32p_row42_tracePolynomial_099
  · exact g32p_row42_tracePolynomial_100
  · exact g32p_row42_tracePolynomial_101

theorem g32p_row42_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 41 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 41 c) := by
  by_cases hc : c ∈ g32p_supplierGroup20_support
  · have hclass (j : Fin 576) :
        IsConj (g32p_literalRepresentative c) (g32p_row26_groupEquiv j : g32p_G) ↔
          g32p_row42_supplierClassifier j = c := by
      simpa only [g32p_row42_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row42_supplierClass_iff (g32p_row26_groupEquiv j) c
    have hχ (j : Fin 576) :
        (g32p_recordedSupplierCharacters 41 (g32p_row26_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row42_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 41 (show (g32p_recordedSuppliers 41).H from g32p_row26_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row42_characterValues (g32p_row26_groupEquiv.symm (g32p_row26_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 41).H (g32p_recordedSupplierCharacters 41)
      (g32p_literalRepresentative c) g32p_row26_groupEquiv g32p_row42_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row42_characterValues j)).val) c 3 576
      (g32p_literalCentralizer c) (g32p_literalTraceValue 41 c) [1, 1, 1]
      (g32p_row42_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row42_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 41)))
      (g32p_row42_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row42_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row42_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row42_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row42_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_0 r
  · exact g32p_row42_variantArithmetic_01_0 r
  · exact g32p_row42_variantArithmetic_02_0 r
  · exact g32p_row42_variantArithmetic_03_0 r
  · exact g32p_row42_variantArithmetic_04_0 r
  · exact g32p_row42_variantArithmetic_05_0 r
  · exact g32p_row42_variantArithmetic_06_0 r

theorem g32p_row42_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_1 r
  · exact g32p_row42_variantArithmetic_01_1 r
  · exact g32p_row42_variantArithmetic_02_1 r
  · exact g32p_row42_variantArithmetic_03_1 r
  · exact g32p_row42_variantArithmetic_04_1 r
  · exact g32p_row42_variantArithmetic_05_1 r
  · exact g32p_row42_variantArithmetic_06_1 r

theorem g32p_row42_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_2 r
  · exact g32p_row42_variantArithmetic_01_2 r
  · exact g32p_row42_variantArithmetic_02_2 r
  · exact g32p_row42_variantArithmetic_03_2 r
  · exact g32p_row42_variantArithmetic_04_2 r
  · exact g32p_row42_variantArithmetic_05_2 r
  · exact g32p_row42_variantArithmetic_06_2 r

theorem g32p_row42_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_3 r
  · exact g32p_row42_variantArithmetic_01_3 r
  · exact g32p_row42_variantArithmetic_02_3 r
  · exact g32p_row42_variantArithmetic_03_3 r
  · exact g32p_row42_variantArithmetic_04_3 r
  · exact g32p_row42_variantArithmetic_05_3 r
  · exact g32p_row42_variantArithmetic_06_3 r

theorem g32p_row42_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_4 r
  · exact g32p_row42_variantArithmetic_01_4 r
  · exact g32p_row42_variantArithmetic_02_4 r
  · exact g32p_row42_variantArithmetic_03_4 r
  · exact g32p_row42_variantArithmetic_04_4 r
  · exact g32p_row42_variantArithmetic_05_4 r
  · exact g32p_row42_variantArithmetic_06_4 r

theorem g32p_row42_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_5 r
  · exact g32p_row42_variantArithmetic_01_5 r
  · exact g32p_row42_variantArithmetic_02_5 r
  · exact g32p_row42_variantArithmetic_03_5 r
  · exact g32p_row42_variantArithmetic_04_5 r
  · exact g32p_row42_variantArithmetic_05_5 r
  · exact g32p_row42_variantArithmetic_06_5 r

theorem g32p_row42_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_6 r
  · exact g32p_row42_variantArithmetic_01_6 r
  · exact g32p_row42_variantArithmetic_02_6 r
  · exact g32p_row42_variantArithmetic_03_6 r
  · exact g32p_row42_variantArithmetic_04_6 r
  · exact g32p_row42_variantArithmetic_05_6 r
  · exact g32p_row42_variantArithmetic_06_6 r

theorem g32p_row42_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row42_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 41 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row42_variantArithmetic_00_7 r
  · exact g32p_row42_variantArithmetic_01_7 r
  · exact g32p_row42_variantArithmetic_02_7 r
  · exact g32p_row42_variantArithmetic_03_7 r
  · exact g32p_row42_variantArithmetic_04_7 r
  · exact g32p_row42_variantArithmetic_05_7 r
  · exact g32p_row42_variantArithmetic_06_7 r

theorem g32p_row42_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row42_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row42_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 41 c _ (g32p_row42_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row42_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row43_supplierClassifier : Fin 432 → Fin 102 := g32p_supplierGroup24_classify

theorem g32p_row43_groupEquiv_isConj (i : Fin 432) :
    IsConj (g32p_row33_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row43_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2
  rw [g32p_supplierGroup24_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row33_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup24_matrix i)

def g32p_row43_supplierClass (h : (g32p_recordedSuppliers 42).H) : Fin 102 :=
  g32p_row43_supplierClassifier (g32p_row33_groupEquiv.symm h)

theorem g32p_row43_supplierClass_isConj (h : (g32p_recordedSuppliers 42).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row43_supplierClass h)) := by
  have he : (g32p_row33_groupEquiv (g32p_row33_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 42).H => (a : g32p_G))
      (g32p_row33_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row43_supplierClassifier (g32p_row33_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row43_groupEquiv_isConj (g32p_row33_groupEquiv.symm h)

theorem g32p_row43_supplierClass_iff (h : (g32p_recordedSuppliers 42).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row43_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row43_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row43_supplierClass_isConj h).symm

theorem g32p_row43_supplierClass_mem_support (h : (g32p_recordedSuppliers 42).H) :
    g32p_row43_supplierClass h ∈ g32p_supplierGroup24_support :=
  g32p_supplierGroup24_support_mem (g32p_row33_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row43_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 0) (g32p_literalTraceValue 42 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_000]
  decide +kernel

theorem g32p_row43_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 1 = [5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 1) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 1) (g32p_literalTraceValue 42 1)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_001]
  decide +kernel

theorem g32p_row43_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 2 = [5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 2) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 2) (g32p_literalTraceValue 42 2)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_002]
  decide +kernel

theorem g32p_row43_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 3 = [4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 3) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 3) (g32p_literalTraceValue 42 3)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_003]
  decide +kernel

theorem g32p_row43_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 4 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 4) (g32p_literalTraceValue 42 4)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_004]
  decide +kernel

theorem g32p_row43_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 5) (g32p_literalTraceValue 42 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_005]
  decide +kernel

theorem g32p_row43_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 6 = [8] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 6) (g32p_literalTraceValue 42 6)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_006]
  decide +kernel

theorem g32p_row43_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 7 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 7) (g32p_literalTraceValue 42 7)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_007]
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

theorem g32p_row43_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 8 = [4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 8) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 8) (g32p_literalTraceValue 42 8)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_008]
  decide +kernel

theorem g32p_row43_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 10 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 10) (g32p_literalTraceValue 42 10)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_010]
  decide +kernel

theorem g32p_row43_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 11 = [4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 11) (g32p_literalTraceValue 42 11)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_011]
  decide +kernel

theorem g32p_row43_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 15 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 15) (g32p_literalTraceValue 42 15)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_015]
  decide +kernel

theorem g32p_row43_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 17 = [0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 17) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 17) (g32p_literalTraceValue 42 17)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_017]
  decide +kernel

theorem g32p_row43_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 18 = [1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 18) (g32p_literalTraceValue 42 18)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_018]
  decide +kernel

theorem g32p_row43_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 19 = [0, 4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 19) (g32p_literalTraceValue 42 19)
      [1, -1, 1] [-1296, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_019]
  decide +kernel

theorem g32p_row43_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 20 = [0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 20) (g32p_literalTraceValue 42 20)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_020]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
