import HodgeLean.Foundations.Program.G32PropFourSixPacked0388
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0390
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0389
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow23
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row22_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row22_supplierClassifier (Fin.ofNat 576 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row22_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row22_traceSegment_101_0000_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 0 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0009_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 9 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0000_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 0 9 9, g32p_row22_traceSegment_101_0000_0009, g32p_row22_traceSegment_101_0009_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0018_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 18 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0027_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 27 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0018_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 18 9 9, g32p_row22_traceSegment_101_0018_0009, g32p_row22_traceSegment_101_0027_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0000_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 0 18 18, g32p_row22_traceSegment_101_0000_0018, g32p_row22_traceSegment_101_0018_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0036_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 36 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0045_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 45 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0036_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 36 9 9, g32p_row22_traceSegment_101_0036_0009, g32p_row22_traceSegment_101_0045_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0054_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 54 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0063_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 63 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0054_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 54 9 9, g32p_row22_traceSegment_101_0054_0009, g32p_row22_traceSegment_101_0063_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0036_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 36 18 18, g32p_row22_traceSegment_101_0036_0018, g32p_row22_traceSegment_101_0054_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0000_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 0 36 36, g32p_row22_traceSegment_101_0000_0036, g32p_row22_traceSegment_101_0036_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0072_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 72 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0081_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 81 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0072_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 72 9 9, g32p_row22_traceSegment_101_0072_0009, g32p_row22_traceSegment_101_0081_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0090_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 90 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0099_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 99 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0090_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 90 9 9, g32p_row22_traceSegment_101_0090_0009, g32p_row22_traceSegment_101_0099_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0072_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 72 18 18, g32p_row22_traceSegment_101_0072_0018, g32p_row22_traceSegment_101_0090_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0108_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 108 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0117_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 117 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0108_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 108 9 9, g32p_row22_traceSegment_101_0108_0009, g32p_row22_traceSegment_101_0117_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0126_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 126 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0135_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 135 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0126_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 126 9 9, g32p_row22_traceSegment_101_0126_0009, g32p_row22_traceSegment_101_0135_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0108_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 108 18 18, g32p_row22_traceSegment_101_0108_0018, g32p_row22_traceSegment_101_0126_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0072_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 72 36 36, g32p_row22_traceSegment_101_0072_0036, g32p_row22_traceSegment_101_0108_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0000_0144 : g32p_coeffSegment g32p_row22_traceSegment_101 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 0 72 72, g32p_row22_traceSegment_101_0000_0072, g32p_row22_traceSegment_101_0072_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0144_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 144 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0153_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 153 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0144_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 144 9 9, g32p_row22_traceSegment_101_0144_0009, g32p_row22_traceSegment_101_0153_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0162_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 162 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0171_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 171 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0162_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 162 9 9, g32p_row22_traceSegment_101_0162_0009, g32p_row22_traceSegment_101_0171_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0144_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 144 18 18, g32p_row22_traceSegment_101_0144_0018, g32p_row22_traceSegment_101_0162_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0180_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 180 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0189_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 189 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0180_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 180 9 9, g32p_row22_traceSegment_101_0180_0009, g32p_row22_traceSegment_101_0189_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0198_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 198 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0207_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 207 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0198_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 198 9 9, g32p_row22_traceSegment_101_0198_0009, g32p_row22_traceSegment_101_0207_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0180_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 180 18 18, g32p_row22_traceSegment_101_0180_0018, g32p_row22_traceSegment_101_0198_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0144_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 144 36 36, g32p_row22_traceSegment_101_0144_0036, g32p_row22_traceSegment_101_0180_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0216_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 216 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0225_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 225 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0216_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 216 9 9, g32p_row22_traceSegment_101_0216_0009, g32p_row22_traceSegment_101_0225_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0234_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 234 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0243_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 243 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0234_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 234 9 9, g32p_row22_traceSegment_101_0234_0009, g32p_row22_traceSegment_101_0243_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0216_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 216 18 18, g32p_row22_traceSegment_101_0216_0018, g32p_row22_traceSegment_101_0234_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0252_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 252 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0261_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 261 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0252_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 252 9 9, g32p_row22_traceSegment_101_0252_0009, g32p_row22_traceSegment_101_0261_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0270_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 270 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0279_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 279 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0270_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 270 9 9, g32p_row22_traceSegment_101_0270_0009, g32p_row22_traceSegment_101_0279_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0252_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 252 18 18, g32p_row22_traceSegment_101_0252_0018, g32p_row22_traceSegment_101_0270_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0216_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 216 36 36, g32p_row22_traceSegment_101_0216_0036, g32p_row22_traceSegment_101_0252_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0144_0144 : g32p_coeffSegment g32p_row22_traceSegment_101 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 144 72 72, g32p_row22_traceSegment_101_0144_0072, g32p_row22_traceSegment_101_0216_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0000_0288 : g32p_coeffSegment g32p_row22_traceSegment_101 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 0 144 144, g32p_row22_traceSegment_101_0000_0144, g32p_row22_traceSegment_101_0144_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0288_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 288 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0297_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 297 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0288_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 288 9 9, g32p_row22_traceSegment_101_0288_0009, g32p_row22_traceSegment_101_0297_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0306_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 306 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0315_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 315 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0306_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 306 9 9, g32p_row22_traceSegment_101_0306_0009, g32p_row22_traceSegment_101_0315_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0288_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 288 18 18, g32p_row22_traceSegment_101_0288_0018, g32p_row22_traceSegment_101_0306_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0324_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 324 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0333_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 333 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0324_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 324 9 9, g32p_row22_traceSegment_101_0324_0009, g32p_row22_traceSegment_101_0333_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0342_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 342 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0351_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 351 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0342_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 342 9 9, g32p_row22_traceSegment_101_0342_0009, g32p_row22_traceSegment_101_0351_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0324_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 324 18 18, g32p_row22_traceSegment_101_0324_0018, g32p_row22_traceSegment_101_0342_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0288_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 288 36 36, g32p_row22_traceSegment_101_0288_0036, g32p_row22_traceSegment_101_0324_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0360_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 360 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0369_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 369 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0360_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 360 9 9, g32p_row22_traceSegment_101_0360_0009, g32p_row22_traceSegment_101_0369_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0378_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 378 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0387_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 387 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0378_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 378 9 9, g32p_row22_traceSegment_101_0378_0009, g32p_row22_traceSegment_101_0387_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0360_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 360 18 18, g32p_row22_traceSegment_101_0360_0018, g32p_row22_traceSegment_101_0378_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0396_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 396 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0405_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 405 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0396_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 396 9 9, g32p_row22_traceSegment_101_0396_0009, g32p_row22_traceSegment_101_0405_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0414_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 414 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0423_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 423 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0414_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 414 9 9, g32p_row22_traceSegment_101_0414_0009, g32p_row22_traceSegment_101_0423_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0396_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 396 18 18, g32p_row22_traceSegment_101_0396_0018, g32p_row22_traceSegment_101_0414_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0360_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 360 36 36, g32p_row22_traceSegment_101_0360_0036, g32p_row22_traceSegment_101_0396_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0288_0144 : g32p_coeffSegment g32p_row22_traceSegment_101 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 288 72 72, g32p_row22_traceSegment_101_0288_0072, g32p_row22_traceSegment_101_0360_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0432_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 432 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0441_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 441 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0432_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 432 9 9, g32p_row22_traceSegment_101_0432_0009, g32p_row22_traceSegment_101_0441_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0450_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 450 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0459_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 459 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0450_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 450 9 9, g32p_row22_traceSegment_101_0450_0009, g32p_row22_traceSegment_101_0459_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0432_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 432 18 18, g32p_row22_traceSegment_101_0432_0018, g32p_row22_traceSegment_101_0450_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0468_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 468 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0477_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 477 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0468_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 468 9 9, g32p_row22_traceSegment_101_0468_0009, g32p_row22_traceSegment_101_0477_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0486_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 486 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0495_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 495 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0486_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 486 9 9, g32p_row22_traceSegment_101_0486_0009, g32p_row22_traceSegment_101_0495_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0468_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 468 18 18, g32p_row22_traceSegment_101_0468_0018, g32p_row22_traceSegment_101_0486_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0432_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 432 36 36, g32p_row22_traceSegment_101_0432_0036, g32p_row22_traceSegment_101_0468_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0504_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 504 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0513_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 513 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0504_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 504 9 9, g32p_row22_traceSegment_101_0504_0009, g32p_row22_traceSegment_101_0513_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0522_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 522 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0531_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 531 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0522_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 522 9 9, g32p_row22_traceSegment_101_0522_0009, g32p_row22_traceSegment_101_0531_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0504_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 504 18 18, g32p_row22_traceSegment_101_0504_0018, g32p_row22_traceSegment_101_0522_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0540_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 540 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0549_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 549 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0540_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 540 9 9, g32p_row22_traceSegment_101_0540_0009, g32p_row22_traceSegment_101_0549_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0558_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 558 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0567_0009 : g32p_coeffSegment g32p_row22_traceSegment_101 567 9 = [] := by
  decide +kernel

private theorem g32p_row22_traceSegment_101_0558_0018 : g32p_coeffSegment g32p_row22_traceSegment_101 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 558 9 9, g32p_row22_traceSegment_101_0558_0009, g32p_row22_traceSegment_101_0567_0009]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0540_0036 : g32p_coeffSegment g32p_row22_traceSegment_101 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 540 18 18, g32p_row22_traceSegment_101_0540_0018, g32p_row22_traceSegment_101_0558_0018]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0504_0072 : g32p_coeffSegment g32p_row22_traceSegment_101 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 504 36 36, g32p_row22_traceSegment_101_0504_0036, g32p_row22_traceSegment_101_0540_0036]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0432_0144 : g32p_coeffSegment g32p_row22_traceSegment_101 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 432 72 72, g32p_row22_traceSegment_101_0432_0072, g32p_row22_traceSegment_101_0504_0072]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0288_0288 : g32p_coeffSegment g32p_row22_traceSegment_101 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 288 144 144, g32p_row22_traceSegment_101_0288_0144, g32p_row22_traceSegment_101_0432_0144]
  decide +kernel

private theorem g32p_row22_traceSegment_101_0000_0576 : g32p_coeffSegment g32p_row22_traceSegment_101 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row22_traceSegment_101 0 288 288, g32p_row22_traceSegment_101_0000_0288, g32p_row22_traceSegment_101_0288_0288]
  decide +kernel

theorem g32p_row22_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row22_traceSegment_101_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row22_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 96) (g32p_literalTraceValue 21 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_096]
  decide +kernel

theorem g32p_row22_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 97) (g32p_literalTraceValue 21 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_097]
  decide +kernel

theorem g32p_row22_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 99) (g32p_literalTraceValue 21 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row22_traceCoefficients_099]
  decide +kernel

theorem g32p_row22_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) 101) (g32p_literalTraceValue 21 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row22_traceCoefficients_101]
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

def g32p_row22_generatorIndex : Fin 8 → Fin 408 :=
  ![21, 72, 123, 174, 246, 247, 348, 349]

theorem g32p_row22_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup17_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 21 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 21 g32p_row22_supplierClass
    g32p_row22_supplierClass_isConj g32p_supplierGroup17_support g32p_row22_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row22_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup17_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row22_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 21 c false (g32p_row22_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 21 c true (g32p_row22_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 21 c false (g32p_row22_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 21 c true (g32p_row22_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 21 c false (g32p_row22_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 21 c false (g32p_row22_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 21 c true (g32p_row22_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 21 c true (g32p_row22_coinduced_zero c hc true) 3

theorem g32p_row22_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row22_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row22_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup17_support) :
    g32p_literalTraceValue (g32p_row22_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup17_support →
    g32p_literalTraceValue (g32p_row22_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row22_zeroTrace_block_00 r k
  · exact g32p_row22_zeroTrace_block_01 r k
  · exact g32p_row22_zeroTrace_block_02 r k
  · exact g32p_row22_zeroTrace_block_03 r k
  · exact g32p_row22_zeroTrace_block_04 r k
  · exact g32p_row22_zeroTrace_block_05 r k
  · exact g32p_row22_zeroTrace_block_06 r k

theorem g32p_row22_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup17_support) :
    (g32p_recordedInductionGenerators (g32p_row22_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row22_generatorIndex k) c) := by
  rw [g32p_row22_recordedGenerator_zero c hc k, g32p_row22_zeroTrace_arithmetic c k hc]
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

def g32p_row22_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [5184, 5184, 5184] else [3456, 3456]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 6912, 6912] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [1728, 1728, 1728] else [576, 576, 576]))) else (if i.val < 34 then (if i.val < 32 then [-3456] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [-1152, 5760, 5760] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [1152, 1152] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 1152, 1152] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [0, 0, 3456, 3456] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [-1152] else (if i.val < 59 then [] else [1728, 1728, 1728])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [17280, 17280, 17280])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [6912, 6912] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [0, 0, 3456, 3456] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [-3456] else [])) else (if i.val < 93 then [5184, 5184, 5184] else (if i.val < 94 then [] else [3456, 3456]))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row22_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup17_support) :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) c) (g32p_literalTraceValue 21 c)
      [1, -1, 1] (g32p_row22_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row22_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_004
  · exact g32p_row22_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_024
  · exact g32p_row22_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_029
  · exact g32p_row22_tracePolynomial_030
  · exact g32p_row22_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_037
  · exact g32p_row22_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_049
  · exact g32p_row22_tracePolynomial_050
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_056
  · exact g32p_row22_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_082
  · exact g32p_row22_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_096
  · exact g32p_row22_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row22_tracePolynomial_101

theorem g32p_row22_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 21 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 21 c) := by
  by_cases hc : c ∈ g32p_supplierGroup17_support
  · have hclass (j : Fin 576) :
        IsConj (g32p_literalRepresentative c) (g32p_row22_groupEquiv j : g32p_G) ↔
          g32p_row22_supplierClassifier j = c := by
      simpa only [g32p_row22_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row22_supplierClass_iff (g32p_row22_groupEquiv j) c
    have hχ (j : Fin 576) :
        (g32p_recordedSupplierCharacters 21 (g32p_row22_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row22_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 21 (show (g32p_recordedSuppliers 21).H from g32p_row22_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row22_characterValues (g32p_row22_groupEquiv.symm (g32p_row22_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 21).H (g32p_recordedSupplierCharacters 21)
      (g32p_literalRepresentative c) g32p_row22_groupEquiv g32p_row22_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row22_characterValues j)).val) c 6 576
      (g32p_literalCentralizer c) (g32p_literalTraceValue 21 c) [1, -1, 1]
      (g32p_row22_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row22_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 21)))
      (g32p_row22_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row22_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row22_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row22_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
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

theorem g32p_row22_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_0 r
  · exact g32p_row22_variantArithmetic_01_0 r
  · exact g32p_row22_variantArithmetic_02_0 r
  · exact g32p_row22_variantArithmetic_03_0 r
  · exact g32p_row22_variantArithmetic_04_0 r
  · exact g32p_row22_variantArithmetic_05_0 r
  · exact g32p_row22_variantArithmetic_06_0 r

theorem g32p_row22_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_1 r
  · exact g32p_row22_variantArithmetic_01_1 r
  · exact g32p_row22_variantArithmetic_02_1 r
  · exact g32p_row22_variantArithmetic_03_1 r
  · exact g32p_row22_variantArithmetic_04_1 r
  · exact g32p_row22_variantArithmetic_05_1 r
  · exact g32p_row22_variantArithmetic_06_1 r

theorem g32p_row22_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_2 r
  · exact g32p_row22_variantArithmetic_01_2 r
  · exact g32p_row22_variantArithmetic_02_2 r
  · exact g32p_row22_variantArithmetic_03_2 r
  · exact g32p_row22_variantArithmetic_04_2 r
  · exact g32p_row22_variantArithmetic_05_2 r
  · exact g32p_row22_variantArithmetic_06_2 r

theorem g32p_row22_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_3 r
  · exact g32p_row22_variantArithmetic_01_3 r
  · exact g32p_row22_variantArithmetic_02_3 r
  · exact g32p_row22_variantArithmetic_03_3 r
  · exact g32p_row22_variantArithmetic_04_3 r
  · exact g32p_row22_variantArithmetic_05_3 r
  · exact g32p_row22_variantArithmetic_06_3 r

theorem g32p_row22_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_4 r
  · exact g32p_row22_variantArithmetic_01_4 r
  · exact g32p_row22_variantArithmetic_02_4 r
  · exact g32p_row22_variantArithmetic_03_4 r
  · exact g32p_row22_variantArithmetic_04_4 r
  · exact g32p_row22_variantArithmetic_05_4 r
  · exact g32p_row22_variantArithmetic_06_4 r

theorem g32p_row22_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_5 r
  · exact g32p_row22_variantArithmetic_01_5 r
  · exact g32p_row22_variantArithmetic_02_5 r
  · exact g32p_row22_variantArithmetic_03_5 r
  · exact g32p_row22_variantArithmetic_04_5 r
  · exact g32p_row22_variantArithmetic_05_5 r
  · exact g32p_row22_variantArithmetic_06_5 r

theorem g32p_row22_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_6 r
  · exact g32p_row22_variantArithmetic_01_6 r
  · exact g32p_row22_variantArithmetic_02_6 r
  · exact g32p_row22_variantArithmetic_03_6 r
  · exact g32p_row22_variantArithmetic_04_6 r
  · exact g32p_row22_variantArithmetic_05_6 r
  · exact g32p_row22_variantArithmetic_06_6 r

theorem g32p_row22_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row22_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 21 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row22_variantArithmetic_00_7 r
  · exact g32p_row22_variantArithmetic_01_7 r
  · exact g32p_row22_variantArithmetic_02_7 r
  · exact g32p_row22_variantArithmetic_03_7 r
  · exact g32p_row22_variantArithmetic_04_7 r
  · exact g32p_row22_variantArithmetic_05_7 r
  · exact g32p_row22_variantArithmetic_06_7 r

theorem g32p_row22_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row22_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row22_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 21 c _ (g32p_row22_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row22_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup18_source : Fin 108 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (105, 126) else (51, 253))) else (if i.val < 4 then (30, 150) else (if i.val < 5 then (0, 99) else (0, 96)))) else (if i.val < 9 then (if i.val < 7 then (15, 58) else (if i.val < 8 then (116, 169) else (19, 212))) else (if i.val < 11 then (if i.val < 10 then (31, 206) else (3, 162)) else (if i.val < 12 then (27, 176) else (14, 66))))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then (7, 89) else (if i.val < 15 then (16, 48) else (56, 144))) else (if i.val < 18 then (if i.val < 17 then (59, 10) else (0, 97)) else (if i.val < 19 then (10, 211) else (111, 24)))) else (if i.val < 23 then (if i.val < 21 then (12, 37) else (if i.val < 22 then (131, 183) else (90, 36))) else (if i.val < 25 then (if i.val < 24 then (59, 140) else (15, 55)) else (if i.val < 26 then (62, 238) else (105, 114)))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then (23, 41) else (if i.val < 29 then (0, 101) else (104, 146))) else (if i.val < 31 then (82, 82) else (if i.val < 32 then (109, 106) else (0, 117)))) else (if i.val < 36 then (if i.val < 34 then (64, 213) else (if i.val < 35 then (0, 212) else (70, 196))) else (if i.val < 38 then (if i.val < 37 then (75, 47) else (5, 216)) else (if i.val < 39 then (95, 143) else (99, 67))))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then (131, 179) else (if i.val < 42 then (140, 48) else (113, 235))) else (if i.val < 45 then (if i.val < 44 then (84, 39) else (49, 110)) else (if i.val < 46 then (4, 145) else (0, 105)))) else (if i.val < 50 then (if i.val < 48 then (62, 90) else (if i.val < 49 then (0, 37) else (55, 147))) else (if i.val < 52 then (if i.val < 51 then (85, 163) else (12, 226)) else (if i.val < 53 then (120, 62) else (117, 57))))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then (5, 182) else (if i.val < 56 then (5, 183) else (64, 17))) else (if i.val < 58 then (108, 213) else (if i.val < 59 then (71, 44) else (130, 91)))) else (if i.val < 63 then (if i.val < 61 then (130, 88) else (if i.val < 62 then (124, 140) else (130, 181))) else (if i.val < 65 then (if i.val < 64 then (85, 87) else (112, 2)) else (if i.val < 66 then (122, 5) else (43, 78))))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then (111, 13) else (if i.val < 69 then (5, 173) else (57, 13))) else (if i.val < 72 then (if i.val < 71 then (80, 45) else (74, 65)) else (if i.val < 73 then (34, 161) else (111, 164)))) else (if i.val < 77 then (if i.val < 75 then (80, 147) else (if i.val < 76 then (43, 109) else (128, 57))) else (if i.val < 79 then (if i.val < 78 then (27, 14) else (53, 108)) else (if i.val < 80 then (112, 148) else (32, 93)))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then (120, 59) else (if i.val < 83 then (57, 241) else (75, 78))) else (if i.val < 85 then (144, 14) else (if i.val < 86 then (65, 185) else (13, 234)))) else (if i.val < 90 then (if i.val < 88 then (1, 178) else (if i.val < 89 then (97, 50) else (31, 121))) else (if i.val < 92 then (if i.val < 91 then (5, 250) else (123, 50)) else (if i.val < 93 then (85, 181) else (9, 156))))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then (79, 246) else (if i.val < 96 then (31, 102) else (111, 255))) else (if i.val < 99 then (if i.val < 98 then (107, 104) else (87, 118)) else (if i.val < 100 then (119, 104) else (66, 181)))) else (if i.val < 104 then (if i.val < 102 then (34, 101) else (if i.val < 103 then (55, 135) else (125, 205))) else (if i.val < 106 then (if i.val < 105 then (0, 64) else (129, 118)) else (if i.val < 107 then (119, 200) else (116, 182))))))))

def g32p_supplierGroup18_classify : Fin 108 → Fin 102 :=
  fun i => (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 65 else 87)) else (if i.val < 4 then 78 else (if i.val < 5 then 99 else 96))) else (if i.val < 9 then (if i.val < 7 then 8 else (if i.val < 8 then 59 else 65)) else (if i.val < 11 then (if i.val < 10 then 100 else 35) else (if i.val < 12 then 88 else 78)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then 24 else (if i.val < 15 then 18 else 76)) else (if i.val < 18 then (if i.val < 17 then 11 else 97) else (if i.val < 19 then 79 else 86))) else (if i.val < 23 then (if i.val < 21 then 81 else (if i.val < 22 then 29 else 59)) else (if i.val < 25 then (if i.val < 24 then 1 else 28) else (if i.val < 26 then 2 else 32))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then 24 else (if i.val < 29 then 101 else 64)) else (if i.val < 31 then 74 else (if i.val < 32 then 18 else 2))) else (if i.val < 36 then (if i.val < 34 then 6 else (if i.val < 35 then 44 else 11)) else (if i.val < 38 then (if i.val < 37 then 56 else 19) else (if i.val < 39 then 23 else 51)))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then 10 else (if i.val < 42 then 29 else 45)) else (if i.val < 45 then (if i.val < 44 then 98 else 93) else (if i.val < 46 then 82 else 1))) else (if i.val < 50 then (if i.val < 48 then 4 else (if i.val < 49 then 37 else 85)) else (if i.val < 52 then (if i.val < 51 then 15 else 91) else (if i.val < 53 then 43 else 74)))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then 87 else (if i.val < 56 then 93 else 67)) else (if i.val < 58 then 75 else (if i.val < 59 then 56 else 71))) else (if i.val < 63 then (if i.val < 61 then 77 else (if i.val < 62 then 85 else 84)) else (if i.val < 65 then (if i.val < 64 then 77 else 25) else (if i.val < 66 then 82 else 67)))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then 45 else (if i.val < 69 then 98 else 4)) else (if i.val < 72 then (if i.val < 71 then 92 else 81) else (if i.val < 73 then 51 else 89))) else (if i.val < 77 then (if i.val < 75 then 66 else (if i.val < 76 then 43 else 35)) else (if i.val < 79 then (if i.val < 78 then 88 else 95) else (if i.val < 80 then 40 else 3))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then 40 else (if i.val < 83 then 19 else 50)) else (if i.val < 85 then 25 else (if i.val < 86 then 76 else 95))) else (if i.val < 90 then (if i.val < 88 then 100 else (if i.val < 89 then 84 else 92)) else (if i.val < 92 then (if i.val < 91 then 10 else 8) else (if i.val < 93 then 3 else 32)))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then 91 else (if i.val < 96 then 89 else 23)) else (if i.val < 99 then (if i.val < 98 then 71 else 50) else (if i.val < 100 then 6 else 44))) else (if i.val < 104 then (if i.val < 102 then 28 else (if i.val < 103 then 86 else 66)) else (if i.val < 106 then (if i.val < 105 then 64 else 79) else (if i.val < 107 then 75 else 15)))))))

def g32p_supplierGroup18_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 6, 8, 10, 11, 15, 18, 19, 23, 24, 25, 28, 29, 32, 35, 37, 40, 43, 44, 45, 50, 51, 56, 59, 64, 65, 66, 67, 71, 74, 75, 76, 77, 78, 79, 81, 82, 84, 85, 86, 87, 88, 89, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup18_matrix_000 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 0 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 0 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 0 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 0 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 0 r) ∈ g32p_supplierGroup18_support := by
  decide +kernel

theorem g32p_supplierGroup18_matrix_001 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 1 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 1 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 1 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 1 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 1 r) ∈ g32p_supplierGroup18_support := by
  decide +kernel

theorem g32p_supplierGroup18_matrix_002 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 2 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 2 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 2 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 2 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 2 r) ∈ g32p_supplierGroup18_support := by
  decide +kernel

theorem g32p_supplierGroup18_matrix_003 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 3 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 3 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 3 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 3 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 3 r) ∈ g32p_supplierGroup18_support := by
  decide +kernel

theorem g32p_supplierGroup18_matrix_004 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 4 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 4 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 4 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 4 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 4 r) ∈ g32p_supplierGroup18_support := by
  decide +kernel

theorem g32p_supplierGroup18_matrix_005 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 5 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 5 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 5 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 5 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 5 r) ∈ g32p_supplierGroup18_support := by
  decide +kernel

theorem g32p_supplierGroup18_matrix_006 : ∀ r : Fin 16,
    g32p_row23_groupNodes (g32p_finBlockIndex 108 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 6 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup18_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup18_source (g32p_finBlockIndex 108 6 r)).1 (g32p_supplierGroup18_source (g32p_finBlockIndex 108 6 r)).2 =
      g32p_supplierGroup18_classify (g32p_finBlockIndex 108 6 r) := by
  decide +kernel

theorem g32p_supplierGroup18_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup18_classify (g32p_finBlockIndex 108 6 r) ∈ g32p_supplierGroup18_support := by
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

theorem g32p_supplierGroup18_matrix (i : Fin 108) :
    g32p_row23_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source i).1 (g32p_supplierGroup18_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row23_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup18_source i).1 (g32p_supplierGroup18_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup18_matrix_000 r
  · exact g32p_supplierGroup18_matrix_001 r
  · exact g32p_supplierGroup18_matrix_002 r
  · exact g32p_supplierGroup18_matrix_003 r
  · exact g32p_supplierGroup18_matrix_004 r
  · exact g32p_supplierGroup18_matrix_005 r
  · exact g32p_supplierGroup18_matrix_006 r

theorem g32p_supplierGroup18_class (i : Fin 108) :
    g32p_supplierForest_classes (g32p_supplierGroup18_source i).1 (g32p_supplierGroup18_source i).2 =
      g32p_supplierGroup18_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup18_source i).1 (g32p_supplierGroup18_source i).2 =
      g32p_supplierGroup18_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup18_class_000 r
  · exact g32p_supplierGroup18_class_001 r
  · exact g32p_supplierGroup18_class_002 r
  · exact g32p_supplierGroup18_class_003 r
  · exact g32p_supplierGroup18_class_004 r
  · exact g32p_supplierGroup18_class_005 r
  · exact g32p_supplierGroup18_class_006 r

theorem g32p_supplierGroup18_support_mem (i : Fin 108) :
    g32p_supplierGroup18_classify i ∈ g32p_supplierGroup18_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup18_classify i ∈ g32p_supplierGroup18_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup18_support_000 r
  · exact g32p_supplierGroup18_support_001 r
  · exact g32p_supplierGroup18_support_002 r
  · exact g32p_supplierGroup18_support_003 r
  · exact g32p_supplierGroup18_support_004 r
  · exact g32p_supplierGroup18_support_005 r
  · exact g32p_supplierGroup18_support_006 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row23_supplierClassifier : Fin 108 → Fin 102 := g32p_supplierGroup18_classify

theorem g32p_row23_groupEquiv_isConj (i : Fin 108) :
    IsConj (g32p_row23_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row23_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup18_source i).1 (g32p_supplierGroup18_source i).2
  rw [g32p_supplierGroup18_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row23_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup18_matrix i)

def g32p_row23_supplierClass (h : (g32p_recordedSuppliers 22).H) : Fin 102 :=
  g32p_row23_supplierClassifier (g32p_row23_groupEquiv.symm h)

theorem g32p_row23_supplierClass_isConj (h : (g32p_recordedSuppliers 22).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row23_supplierClass h)) := by
  have he : (g32p_row23_groupEquiv (g32p_row23_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 22).H => (a : g32p_G))
      (g32p_row23_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row23_supplierClassifier (g32p_row23_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row23_groupEquiv_isConj (g32p_row23_groupEquiv.symm h)

theorem g32p_row23_supplierClass_iff (h : (g32p_recordedSuppliers 22).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row23_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row23_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row23_supplierClass_isConj h).symm

theorem g32p_row23_supplierClass_mem_support (h : (g32p_recordedSuppliers 22).H) :
    g32p_row23_supplierClass h ∈ g32p_supplierGroup18_support :=
  g32p_supplierGroup18_support_mem (g32p_row23_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end
