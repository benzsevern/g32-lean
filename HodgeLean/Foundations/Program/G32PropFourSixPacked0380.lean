import HodgeLean.Foundations.Program.G32PropFourSixPacked0376
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0377
import HodgeLean.Foundations.Program.G32PropFourSixPacked0378
import HodgeLean.Foundations.Program.G32PropFourSixPacked0379
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow20
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_096_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 9 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 0 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 9 9, g32p_row19_traceSegment_096_0000_0009, g32p_row19_traceSegment_096_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 18 9 9, g32p_row19_traceSegment_096_0018_0009, g32p_row19_traceSegment_096_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 18 18, g32p_row19_traceSegment_096_0000_0018, g32p_row19_traceSegment_096_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 36 9 9, g32p_row19_traceSegment_096_0036_0009, g32p_row19_traceSegment_096_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 54 9 9, g32p_row19_traceSegment_096_0054_0009, g32p_row19_traceSegment_096_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 36 18 18, g32p_row19_traceSegment_096_0036_0018, g32p_row19_traceSegment_096_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 36 36, g32p_row19_traceSegment_096_0000_0036, g32p_row19_traceSegment_096_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 72 9 9, g32p_row19_traceSegment_096_0072_0009, g32p_row19_traceSegment_096_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 90 9 9, g32p_row19_traceSegment_096_0090_0009, g32p_row19_traceSegment_096_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 72 18 18, g32p_row19_traceSegment_096_0072_0018, g32p_row19_traceSegment_096_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 108 9 9, g32p_row19_traceSegment_096_0108_0009, g32p_row19_traceSegment_096_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 126 9 9, g32p_row19_traceSegment_096_0126_0009, g32p_row19_traceSegment_096_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 108 18 18, g32p_row19_traceSegment_096_0108_0018, g32p_row19_traceSegment_096_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 72 36 36, g32p_row19_traceSegment_096_0072_0036, g32p_row19_traceSegment_096_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 72 72, g32p_row19_traceSegment_096_0000_0072, g32p_row19_traceSegment_096_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 144 9 9, g32p_row19_traceSegment_096_0144_0009, g32p_row19_traceSegment_096_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 162 9 9, g32p_row19_traceSegment_096_0162_0009, g32p_row19_traceSegment_096_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 144 18 18, g32p_row19_traceSegment_096_0144_0018, g32p_row19_traceSegment_096_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 180 9 9, g32p_row19_traceSegment_096_0180_0009, g32p_row19_traceSegment_096_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 198 9 9, g32p_row19_traceSegment_096_0198_0009, g32p_row19_traceSegment_096_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 180 18 18, g32p_row19_traceSegment_096_0180_0018, g32p_row19_traceSegment_096_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 144 36 36, g32p_row19_traceSegment_096_0144_0036, g32p_row19_traceSegment_096_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 216 9 9, g32p_row19_traceSegment_096_0216_0009, g32p_row19_traceSegment_096_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 234 9 9, g32p_row19_traceSegment_096_0234_0009, g32p_row19_traceSegment_096_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 216 18 18, g32p_row19_traceSegment_096_0216_0018, g32p_row19_traceSegment_096_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 252 9 9, g32p_row19_traceSegment_096_0252_0009, g32p_row19_traceSegment_096_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 270 9 9, g32p_row19_traceSegment_096_0270_0009, g32p_row19_traceSegment_096_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 252 18 18, g32p_row19_traceSegment_096_0252_0018, g32p_row19_traceSegment_096_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 216 36 36, g32p_row19_traceSegment_096_0216_0036, g32p_row19_traceSegment_096_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 144 72 72, g32p_row19_traceSegment_096_0144_0072, g32p_row19_traceSegment_096_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_096 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 144 144, g32p_row19_traceSegment_096_0000_0144, g32p_row19_traceSegment_096_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 288 9 9, g32p_row19_traceSegment_096_0288_0009, g32p_row19_traceSegment_096_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 306 9 9, g32p_row19_traceSegment_096_0306_0009, g32p_row19_traceSegment_096_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 288 18 18, g32p_row19_traceSegment_096_0288_0018, g32p_row19_traceSegment_096_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 324 9 9, g32p_row19_traceSegment_096_0324_0009, g32p_row19_traceSegment_096_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 342 9 9, g32p_row19_traceSegment_096_0342_0009, g32p_row19_traceSegment_096_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 324 18 18, g32p_row19_traceSegment_096_0324_0018, g32p_row19_traceSegment_096_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 288 36 36, g32p_row19_traceSegment_096_0288_0036, g32p_row19_traceSegment_096_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 360 9 9, g32p_row19_traceSegment_096_0360_0009, g32p_row19_traceSegment_096_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 378 9 9, g32p_row19_traceSegment_096_0378_0009, g32p_row19_traceSegment_096_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 360 18 18, g32p_row19_traceSegment_096_0360_0018, g32p_row19_traceSegment_096_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 396 9 9, g32p_row19_traceSegment_096_0396_0009, g32p_row19_traceSegment_096_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 414 9 9, g32p_row19_traceSegment_096_0414_0009, g32p_row19_traceSegment_096_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 396 18 18, g32p_row19_traceSegment_096_0396_0018, g32p_row19_traceSegment_096_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 360 36 36, g32p_row19_traceSegment_096_0360_0036, g32p_row19_traceSegment_096_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 288 72 72, g32p_row19_traceSegment_096_0288_0072, g32p_row19_traceSegment_096_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 432 9 9, g32p_row19_traceSegment_096_0432_0009, g32p_row19_traceSegment_096_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 450 9 9, g32p_row19_traceSegment_096_0450_0009, g32p_row19_traceSegment_096_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 432 18 18, g32p_row19_traceSegment_096_0432_0018, g32p_row19_traceSegment_096_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 468 9 9, g32p_row19_traceSegment_096_0468_0009, g32p_row19_traceSegment_096_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 486 9 9, g32p_row19_traceSegment_096_0486_0009, g32p_row19_traceSegment_096_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 468 18 18, g32p_row19_traceSegment_096_0468_0018, g32p_row19_traceSegment_096_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 432 36 36, g32p_row19_traceSegment_096_0432_0036, g32p_row19_traceSegment_096_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 504 9 9, g32p_row19_traceSegment_096_0504_0009, g32p_row19_traceSegment_096_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 522 9 9, g32p_row19_traceSegment_096_0522_0009, g32p_row19_traceSegment_096_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 504 18 18, g32p_row19_traceSegment_096_0504_0018, g32p_row19_traceSegment_096_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 540 9 9, g32p_row19_traceSegment_096_0540_0009, g32p_row19_traceSegment_096_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 558 9 9, g32p_row19_traceSegment_096_0558_0009, g32p_row19_traceSegment_096_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 540 18 18, g32p_row19_traceSegment_096_0540_0018, g32p_row19_traceSegment_096_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 504 36 36, g32p_row19_traceSegment_096_0504_0036, g32p_row19_traceSegment_096_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 432 72 72, g32p_row19_traceSegment_096_0432_0072, g32p_row19_traceSegment_096_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_096 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 288 144 144, g32p_row19_traceSegment_096_0288_0144, g32p_row19_traceSegment_096_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_096 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 288 288, g32p_row19_traceSegment_096_0000_0288, g32p_row19_traceSegment_096_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 576 9 9, g32p_row19_traceSegment_096_0576_0009, g32p_row19_traceSegment_096_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 594 9 9, g32p_row19_traceSegment_096_0594_0009, g32p_row19_traceSegment_096_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 576 18 18, g32p_row19_traceSegment_096_0576_0018, g32p_row19_traceSegment_096_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 612 9 9, g32p_row19_traceSegment_096_0612_0009, g32p_row19_traceSegment_096_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 630 9 9, g32p_row19_traceSegment_096_0630_0009, g32p_row19_traceSegment_096_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 612 18 18, g32p_row19_traceSegment_096_0612_0018, g32p_row19_traceSegment_096_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 576 36 36, g32p_row19_traceSegment_096_0576_0036, g32p_row19_traceSegment_096_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 648 9 9, g32p_row19_traceSegment_096_0648_0009, g32p_row19_traceSegment_096_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 666 9 9, g32p_row19_traceSegment_096_0666_0009, g32p_row19_traceSegment_096_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 648 18 18, g32p_row19_traceSegment_096_0648_0018, g32p_row19_traceSegment_096_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 684 9 9, g32p_row19_traceSegment_096_0684_0009, g32p_row19_traceSegment_096_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 702 9 9, g32p_row19_traceSegment_096_0702_0009, g32p_row19_traceSegment_096_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 684 18 18, g32p_row19_traceSegment_096_0684_0018, g32p_row19_traceSegment_096_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 648 36 36, g32p_row19_traceSegment_096_0648_0036, g32p_row19_traceSegment_096_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 576 72 72, g32p_row19_traceSegment_096_0576_0072, g32p_row19_traceSegment_096_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 720 9 9, g32p_row19_traceSegment_096_0720_0009, g32p_row19_traceSegment_096_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 738 9 9, g32p_row19_traceSegment_096_0738_0009, g32p_row19_traceSegment_096_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 720 18 18, g32p_row19_traceSegment_096_0720_0018, g32p_row19_traceSegment_096_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 756 9 9, g32p_row19_traceSegment_096_0756_0009, g32p_row19_traceSegment_096_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 774 9 9, g32p_row19_traceSegment_096_0774_0009, g32p_row19_traceSegment_096_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 756 18 18, g32p_row19_traceSegment_096_0756_0018, g32p_row19_traceSegment_096_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 720 36 36, g32p_row19_traceSegment_096_0720_0036, g32p_row19_traceSegment_096_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 792 9 9, g32p_row19_traceSegment_096_0792_0009, g32p_row19_traceSegment_096_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 810 9 9, g32p_row19_traceSegment_096_0810_0009, g32p_row19_traceSegment_096_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 792 18 18, g32p_row19_traceSegment_096_0792_0018, g32p_row19_traceSegment_096_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 828 9 9, g32p_row19_traceSegment_096_0828_0009, g32p_row19_traceSegment_096_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 846 9 9, g32p_row19_traceSegment_096_0846_0009, g32p_row19_traceSegment_096_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 828 18 18, g32p_row19_traceSegment_096_0828_0018, g32p_row19_traceSegment_096_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 792 36 36, g32p_row19_traceSegment_096_0792_0036, g32p_row19_traceSegment_096_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 720 72 72, g32p_row19_traceSegment_096_0720_0072, g32p_row19_traceSegment_096_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_096 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 576 144 144, g32p_row19_traceSegment_096_0576_0144, g32p_row19_traceSegment_096_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 864 9 9, g32p_row19_traceSegment_096_0864_0009, g32p_row19_traceSegment_096_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 882 9 9, g32p_row19_traceSegment_096_0882_0009, g32p_row19_traceSegment_096_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 864 18 18, g32p_row19_traceSegment_096_0864_0018, g32p_row19_traceSegment_096_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 900 9 9, g32p_row19_traceSegment_096_0900_0009, g32p_row19_traceSegment_096_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 918 9 9, g32p_row19_traceSegment_096_0918_0009, g32p_row19_traceSegment_096_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 900 18 18, g32p_row19_traceSegment_096_0900_0018, g32p_row19_traceSegment_096_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 864 36 36, g32p_row19_traceSegment_096_0864_0036, g32p_row19_traceSegment_096_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 936 9 9, g32p_row19_traceSegment_096_0936_0009, g32p_row19_traceSegment_096_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 954 9 9, g32p_row19_traceSegment_096_0954_0009, g32p_row19_traceSegment_096_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 936 18 18, g32p_row19_traceSegment_096_0936_0018, g32p_row19_traceSegment_096_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 972 9 9, g32p_row19_traceSegment_096_0972_0009, g32p_row19_traceSegment_096_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 990 9 9, g32p_row19_traceSegment_096_0990_0009, g32p_row19_traceSegment_096_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 972 18 18, g32p_row19_traceSegment_096_0972_0018, g32p_row19_traceSegment_096_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 936 36 36, g32p_row19_traceSegment_096_0936_0036, g32p_row19_traceSegment_096_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 864 72 72, g32p_row19_traceSegment_096_0864_0072, g32p_row19_traceSegment_096_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1008 9 9, g32p_row19_traceSegment_096_1008_0009, g32p_row19_traceSegment_096_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1026 9 9, g32p_row19_traceSegment_096_1026_0009, g32p_row19_traceSegment_096_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1008 18 18, g32p_row19_traceSegment_096_1008_0018, g32p_row19_traceSegment_096_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1044 9 9, g32p_row19_traceSegment_096_1044_0009, g32p_row19_traceSegment_096_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1062 9 9, g32p_row19_traceSegment_096_1062_0009, g32p_row19_traceSegment_096_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1044 18 18, g32p_row19_traceSegment_096_1044_0018, g32p_row19_traceSegment_096_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1008 36 36, g32p_row19_traceSegment_096_1008_0036, g32p_row19_traceSegment_096_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1080 9 9, g32p_row19_traceSegment_096_1080_0009, g32p_row19_traceSegment_096_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1098 9 9, g32p_row19_traceSegment_096_1098_0009, g32p_row19_traceSegment_096_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1080 18 18, g32p_row19_traceSegment_096_1080_0018, g32p_row19_traceSegment_096_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1116 9 9, g32p_row19_traceSegment_096_1116_0009, g32p_row19_traceSegment_096_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_096 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_096_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_096 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1134 9 9, g32p_row19_traceSegment_096_1134_0009, g32p_row19_traceSegment_096_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_096 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1116 18 18, g32p_row19_traceSegment_096_1116_0018, g32p_row19_traceSegment_096_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_096 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1080 36 36, g32p_row19_traceSegment_096_1080_0036, g32p_row19_traceSegment_096_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_096_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_096 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 1008 72 72, g32p_row19_traceSegment_096_1008_0072, g32p_row19_traceSegment_096_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_096 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 864 144 144, g32p_row19_traceSegment_096_0864_0144, g32p_row19_traceSegment_096_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_096 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 576 288 288, g32p_row19_traceSegment_096_0576_0288, g32p_row19_traceSegment_096_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_096_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_096 0 1152 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_096 0 576 576, g32p_row19_traceSegment_096_0000_0576, g32p_row19_traceSegment_096_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_096_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_097_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 9 9, g32p_row19_traceSegment_097_0000_0009, g32p_row19_traceSegment_097_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 27 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 18 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 18 9 9, g32p_row19_traceSegment_097_0018_0009, g32p_row19_traceSegment_097_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 0 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 18 18, g32p_row19_traceSegment_097_0000_0018, g32p_row19_traceSegment_097_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 36 9 9, g32p_row19_traceSegment_097_0036_0009, g32p_row19_traceSegment_097_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 54 9 9, g32p_row19_traceSegment_097_0054_0009, g32p_row19_traceSegment_097_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 36 18 18, g32p_row19_traceSegment_097_0036_0018, g32p_row19_traceSegment_097_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 0 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 36 36, g32p_row19_traceSegment_097_0000_0036, g32p_row19_traceSegment_097_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 72 9 9, g32p_row19_traceSegment_097_0072_0009, g32p_row19_traceSegment_097_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 90 9 9, g32p_row19_traceSegment_097_0090_0009, g32p_row19_traceSegment_097_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 72 18 18, g32p_row19_traceSegment_097_0072_0018, g32p_row19_traceSegment_097_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 108 9 9, g32p_row19_traceSegment_097_0108_0009, g32p_row19_traceSegment_097_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 126 9 9, g32p_row19_traceSegment_097_0126_0009, g32p_row19_traceSegment_097_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 108 18 18, g32p_row19_traceSegment_097_0108_0018, g32p_row19_traceSegment_097_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 72 36 36, g32p_row19_traceSegment_097_0072_0036, g32p_row19_traceSegment_097_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 0 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 72 72, g32p_row19_traceSegment_097_0000_0072, g32p_row19_traceSegment_097_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 144 9 9, g32p_row19_traceSegment_097_0144_0009, g32p_row19_traceSegment_097_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 162 9 9, g32p_row19_traceSegment_097_0162_0009, g32p_row19_traceSegment_097_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 144 18 18, g32p_row19_traceSegment_097_0144_0018, g32p_row19_traceSegment_097_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 180 9 9, g32p_row19_traceSegment_097_0180_0009, g32p_row19_traceSegment_097_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 198 9 9, g32p_row19_traceSegment_097_0198_0009, g32p_row19_traceSegment_097_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 180 18 18, g32p_row19_traceSegment_097_0180_0018, g32p_row19_traceSegment_097_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 144 36 36, g32p_row19_traceSegment_097_0144_0036, g32p_row19_traceSegment_097_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 216 9 9, g32p_row19_traceSegment_097_0216_0009, g32p_row19_traceSegment_097_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 234 9 9, g32p_row19_traceSegment_097_0234_0009, g32p_row19_traceSegment_097_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 216 18 18, g32p_row19_traceSegment_097_0216_0018, g32p_row19_traceSegment_097_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 252 9 9, g32p_row19_traceSegment_097_0252_0009, g32p_row19_traceSegment_097_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 270 9 9, g32p_row19_traceSegment_097_0270_0009, g32p_row19_traceSegment_097_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 252 18 18, g32p_row19_traceSegment_097_0252_0018, g32p_row19_traceSegment_097_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 216 36 36, g32p_row19_traceSegment_097_0216_0036, g32p_row19_traceSegment_097_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 144 72 72, g32p_row19_traceSegment_097_0144_0072, g32p_row19_traceSegment_097_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_097 0 288 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 144 144, g32p_row19_traceSegment_097_0000_0144, g32p_row19_traceSegment_097_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 288 9 9, g32p_row19_traceSegment_097_0288_0009, g32p_row19_traceSegment_097_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 306 9 9, g32p_row19_traceSegment_097_0306_0009, g32p_row19_traceSegment_097_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 288 18 18, g32p_row19_traceSegment_097_0288_0018, g32p_row19_traceSegment_097_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 324 9 9, g32p_row19_traceSegment_097_0324_0009, g32p_row19_traceSegment_097_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 342 9 9, g32p_row19_traceSegment_097_0342_0009, g32p_row19_traceSegment_097_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 324 18 18, g32p_row19_traceSegment_097_0324_0018, g32p_row19_traceSegment_097_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 288 36 36, g32p_row19_traceSegment_097_0288_0036, g32p_row19_traceSegment_097_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 360 9 9, g32p_row19_traceSegment_097_0360_0009, g32p_row19_traceSegment_097_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 378 9 9, g32p_row19_traceSegment_097_0378_0009, g32p_row19_traceSegment_097_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 360 18 18, g32p_row19_traceSegment_097_0360_0018, g32p_row19_traceSegment_097_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 396 9 9, g32p_row19_traceSegment_097_0396_0009, g32p_row19_traceSegment_097_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 414 9 9, g32p_row19_traceSegment_097_0414_0009, g32p_row19_traceSegment_097_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 396 18 18, g32p_row19_traceSegment_097_0396_0018, g32p_row19_traceSegment_097_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 360 36 36, g32p_row19_traceSegment_097_0360_0036, g32p_row19_traceSegment_097_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 288 72 72, g32p_row19_traceSegment_097_0288_0072, g32p_row19_traceSegment_097_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 432 9 9, g32p_row19_traceSegment_097_0432_0009, g32p_row19_traceSegment_097_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 450 9 9, g32p_row19_traceSegment_097_0450_0009, g32p_row19_traceSegment_097_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 432 18 18, g32p_row19_traceSegment_097_0432_0018, g32p_row19_traceSegment_097_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 468 9 9, g32p_row19_traceSegment_097_0468_0009, g32p_row19_traceSegment_097_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 486 9 9, g32p_row19_traceSegment_097_0486_0009, g32p_row19_traceSegment_097_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 468 18 18, g32p_row19_traceSegment_097_0468_0018, g32p_row19_traceSegment_097_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 432 36 36, g32p_row19_traceSegment_097_0432_0036, g32p_row19_traceSegment_097_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 504 9 9, g32p_row19_traceSegment_097_0504_0009, g32p_row19_traceSegment_097_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 522 9 9, g32p_row19_traceSegment_097_0522_0009, g32p_row19_traceSegment_097_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 504 18 18, g32p_row19_traceSegment_097_0504_0018, g32p_row19_traceSegment_097_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 540 9 9, g32p_row19_traceSegment_097_0540_0009, g32p_row19_traceSegment_097_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 558 9 9, g32p_row19_traceSegment_097_0558_0009, g32p_row19_traceSegment_097_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 540 18 18, g32p_row19_traceSegment_097_0540_0018, g32p_row19_traceSegment_097_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 504 36 36, g32p_row19_traceSegment_097_0504_0036, g32p_row19_traceSegment_097_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 432 72 72, g32p_row19_traceSegment_097_0432_0072, g32p_row19_traceSegment_097_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_097 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 288 144 144, g32p_row19_traceSegment_097_0288_0144, g32p_row19_traceSegment_097_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_097 0 576 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 288 288, g32p_row19_traceSegment_097_0000_0288, g32p_row19_traceSegment_097_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 576 9 9, g32p_row19_traceSegment_097_0576_0009, g32p_row19_traceSegment_097_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 594 9 9, g32p_row19_traceSegment_097_0594_0009, g32p_row19_traceSegment_097_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 576 18 18, g32p_row19_traceSegment_097_0576_0018, g32p_row19_traceSegment_097_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 612 9 9, g32p_row19_traceSegment_097_0612_0009, g32p_row19_traceSegment_097_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 630 9 9, g32p_row19_traceSegment_097_0630_0009, g32p_row19_traceSegment_097_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 612 18 18, g32p_row19_traceSegment_097_0612_0018, g32p_row19_traceSegment_097_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 576 36 36, g32p_row19_traceSegment_097_0576_0036, g32p_row19_traceSegment_097_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 648 9 9, g32p_row19_traceSegment_097_0648_0009, g32p_row19_traceSegment_097_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 666 9 9, g32p_row19_traceSegment_097_0666_0009, g32p_row19_traceSegment_097_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 648 18 18, g32p_row19_traceSegment_097_0648_0018, g32p_row19_traceSegment_097_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 684 9 9, g32p_row19_traceSegment_097_0684_0009, g32p_row19_traceSegment_097_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 702 9 9, g32p_row19_traceSegment_097_0702_0009, g32p_row19_traceSegment_097_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 684 18 18, g32p_row19_traceSegment_097_0684_0018, g32p_row19_traceSegment_097_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 648 36 36, g32p_row19_traceSegment_097_0648_0036, g32p_row19_traceSegment_097_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 576 72 72, g32p_row19_traceSegment_097_0576_0072, g32p_row19_traceSegment_097_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 720 9 9, g32p_row19_traceSegment_097_0720_0009, g32p_row19_traceSegment_097_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 738 9 9, g32p_row19_traceSegment_097_0738_0009, g32p_row19_traceSegment_097_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 720 18 18, g32p_row19_traceSegment_097_0720_0018, g32p_row19_traceSegment_097_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 756 9 9, g32p_row19_traceSegment_097_0756_0009, g32p_row19_traceSegment_097_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 774 9 9, g32p_row19_traceSegment_097_0774_0009, g32p_row19_traceSegment_097_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 756 18 18, g32p_row19_traceSegment_097_0756_0018, g32p_row19_traceSegment_097_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 720 36 36, g32p_row19_traceSegment_097_0720_0036, g32p_row19_traceSegment_097_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 792 9 9, g32p_row19_traceSegment_097_0792_0009, g32p_row19_traceSegment_097_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 810 9 9, g32p_row19_traceSegment_097_0810_0009, g32p_row19_traceSegment_097_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 792 18 18, g32p_row19_traceSegment_097_0792_0018, g32p_row19_traceSegment_097_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 828 9 9, g32p_row19_traceSegment_097_0828_0009, g32p_row19_traceSegment_097_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 846 9 9, g32p_row19_traceSegment_097_0846_0009, g32p_row19_traceSegment_097_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 828 18 18, g32p_row19_traceSegment_097_0828_0018, g32p_row19_traceSegment_097_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 792 36 36, g32p_row19_traceSegment_097_0792_0036, g32p_row19_traceSegment_097_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 720 72 72, g32p_row19_traceSegment_097_0720_0072, g32p_row19_traceSegment_097_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_097 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 576 144 144, g32p_row19_traceSegment_097_0576_0144, g32p_row19_traceSegment_097_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 864 9 9, g32p_row19_traceSegment_097_0864_0009, g32p_row19_traceSegment_097_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 882 9 9, g32p_row19_traceSegment_097_0882_0009, g32p_row19_traceSegment_097_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 864 18 18, g32p_row19_traceSegment_097_0864_0018, g32p_row19_traceSegment_097_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 900 9 9, g32p_row19_traceSegment_097_0900_0009, g32p_row19_traceSegment_097_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 918 9 9, g32p_row19_traceSegment_097_0918_0009, g32p_row19_traceSegment_097_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 900 18 18, g32p_row19_traceSegment_097_0900_0018, g32p_row19_traceSegment_097_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 864 36 36, g32p_row19_traceSegment_097_0864_0036, g32p_row19_traceSegment_097_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 936 9 9, g32p_row19_traceSegment_097_0936_0009, g32p_row19_traceSegment_097_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 954 9 9, g32p_row19_traceSegment_097_0954_0009, g32p_row19_traceSegment_097_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 936 18 18, g32p_row19_traceSegment_097_0936_0018, g32p_row19_traceSegment_097_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 972 9 9, g32p_row19_traceSegment_097_0972_0009, g32p_row19_traceSegment_097_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 990 9 9, g32p_row19_traceSegment_097_0990_0009, g32p_row19_traceSegment_097_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 972 18 18, g32p_row19_traceSegment_097_0972_0018, g32p_row19_traceSegment_097_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 936 36 36, g32p_row19_traceSegment_097_0936_0036, g32p_row19_traceSegment_097_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 864 72 72, g32p_row19_traceSegment_097_0864_0072, g32p_row19_traceSegment_097_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1008 9 9, g32p_row19_traceSegment_097_1008_0009, g32p_row19_traceSegment_097_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1026 9 9, g32p_row19_traceSegment_097_1026_0009, g32p_row19_traceSegment_097_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1008 18 18, g32p_row19_traceSegment_097_1008_0018, g32p_row19_traceSegment_097_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1044 9 9, g32p_row19_traceSegment_097_1044_0009, g32p_row19_traceSegment_097_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1062 9 9, g32p_row19_traceSegment_097_1062_0009, g32p_row19_traceSegment_097_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1044 18 18, g32p_row19_traceSegment_097_1044_0018, g32p_row19_traceSegment_097_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1008 36 36, g32p_row19_traceSegment_097_1008_0036, g32p_row19_traceSegment_097_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1080 9 9, g32p_row19_traceSegment_097_1080_0009, g32p_row19_traceSegment_097_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1098 9 9, g32p_row19_traceSegment_097_1098_0009, g32p_row19_traceSegment_097_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1080 18 18, g32p_row19_traceSegment_097_1080_0018, g32p_row19_traceSegment_097_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1116 9 9, g32p_row19_traceSegment_097_1116_0009, g32p_row19_traceSegment_097_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_097 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_097_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_097 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1134 9 9, g32p_row19_traceSegment_097_1134_0009, g32p_row19_traceSegment_097_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_097 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1116 18 18, g32p_row19_traceSegment_097_1116_0018, g32p_row19_traceSegment_097_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_097 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1080 36 36, g32p_row19_traceSegment_097_1080_0036, g32p_row19_traceSegment_097_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_097_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_097 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 1008 72 72, g32p_row19_traceSegment_097_1008_0072, g32p_row19_traceSegment_097_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_097 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 864 144 144, g32p_row19_traceSegment_097_0864_0144, g32p_row19_traceSegment_097_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_097 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 576 288 288, g32p_row19_traceSegment_097_0576_0288, g32p_row19_traceSegment_097_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_097_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_097 0 1152 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_097 0 576 576, g32p_row19_traceSegment_097_0000_0576, g32p_row19_traceSegment_097_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_097_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_099_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 0 9 = [1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 9 9, g32p_row19_traceSegment_099_0000_0009, g32p_row19_traceSegment_099_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 18 9 9, g32p_row19_traceSegment_099_0018_0009, g32p_row19_traceSegment_099_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 18 18, g32p_row19_traceSegment_099_0000_0018, g32p_row19_traceSegment_099_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 36 9 9, g32p_row19_traceSegment_099_0036_0009, g32p_row19_traceSegment_099_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 54 9 9, g32p_row19_traceSegment_099_0054_0009, g32p_row19_traceSegment_099_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 36 18 18, g32p_row19_traceSegment_099_0036_0018, g32p_row19_traceSegment_099_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 36 36, g32p_row19_traceSegment_099_0000_0036, g32p_row19_traceSegment_099_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 72 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 72 9 9, g32p_row19_traceSegment_099_0072_0009, g32p_row19_traceSegment_099_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 90 9 9, g32p_row19_traceSegment_099_0090_0009, g32p_row19_traceSegment_099_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 72 18 18, g32p_row19_traceSegment_099_0072_0018, g32p_row19_traceSegment_099_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 108 9 9, g32p_row19_traceSegment_099_0108_0009, g32p_row19_traceSegment_099_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 126 9 9, g32p_row19_traceSegment_099_0126_0009, g32p_row19_traceSegment_099_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 108 18 18, g32p_row19_traceSegment_099_0108_0018, g32p_row19_traceSegment_099_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 72 36 36, g32p_row19_traceSegment_099_0072_0036, g32p_row19_traceSegment_099_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 72 72, g32p_row19_traceSegment_099_0000_0072, g32p_row19_traceSegment_099_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 144 9 9, g32p_row19_traceSegment_099_0144_0009, g32p_row19_traceSegment_099_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 162 9 9, g32p_row19_traceSegment_099_0162_0009, g32p_row19_traceSegment_099_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 144 18 18, g32p_row19_traceSegment_099_0144_0018, g32p_row19_traceSegment_099_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 180 9 9, g32p_row19_traceSegment_099_0180_0009, g32p_row19_traceSegment_099_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 198 9 9, g32p_row19_traceSegment_099_0198_0009, g32p_row19_traceSegment_099_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 180 18 18, g32p_row19_traceSegment_099_0180_0018, g32p_row19_traceSegment_099_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 144 36 36, g32p_row19_traceSegment_099_0144_0036, g32p_row19_traceSegment_099_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 216 9 9, g32p_row19_traceSegment_099_0216_0009, g32p_row19_traceSegment_099_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 234 9 9, g32p_row19_traceSegment_099_0234_0009, g32p_row19_traceSegment_099_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 216 18 18, g32p_row19_traceSegment_099_0216_0018, g32p_row19_traceSegment_099_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 252 9 9, g32p_row19_traceSegment_099_0252_0009, g32p_row19_traceSegment_099_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 270 9 9, g32p_row19_traceSegment_099_0270_0009, g32p_row19_traceSegment_099_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 252 18 18, g32p_row19_traceSegment_099_0252_0018, g32p_row19_traceSegment_099_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 216 36 36, g32p_row19_traceSegment_099_0216_0036, g32p_row19_traceSegment_099_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 144 72 72, g32p_row19_traceSegment_099_0144_0072, g32p_row19_traceSegment_099_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_099 0 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 144 144, g32p_row19_traceSegment_099_0000_0144, g32p_row19_traceSegment_099_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 288 9 9, g32p_row19_traceSegment_099_0288_0009, g32p_row19_traceSegment_099_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 306 9 9, g32p_row19_traceSegment_099_0306_0009, g32p_row19_traceSegment_099_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 288 18 18, g32p_row19_traceSegment_099_0288_0018, g32p_row19_traceSegment_099_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 324 9 9, g32p_row19_traceSegment_099_0324_0009, g32p_row19_traceSegment_099_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 342 9 9, g32p_row19_traceSegment_099_0342_0009, g32p_row19_traceSegment_099_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 324 18 18, g32p_row19_traceSegment_099_0324_0018, g32p_row19_traceSegment_099_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 288 36 36, g32p_row19_traceSegment_099_0288_0036, g32p_row19_traceSegment_099_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 360 9 9, g32p_row19_traceSegment_099_0360_0009, g32p_row19_traceSegment_099_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 378 9 9, g32p_row19_traceSegment_099_0378_0009, g32p_row19_traceSegment_099_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 360 18 18, g32p_row19_traceSegment_099_0360_0018, g32p_row19_traceSegment_099_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 396 9 9, g32p_row19_traceSegment_099_0396_0009, g32p_row19_traceSegment_099_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 414 9 9, g32p_row19_traceSegment_099_0414_0009, g32p_row19_traceSegment_099_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 396 18 18, g32p_row19_traceSegment_099_0396_0018, g32p_row19_traceSegment_099_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 360 36 36, g32p_row19_traceSegment_099_0360_0036, g32p_row19_traceSegment_099_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 288 72 72, g32p_row19_traceSegment_099_0288_0072, g32p_row19_traceSegment_099_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 432 9 9, g32p_row19_traceSegment_099_0432_0009, g32p_row19_traceSegment_099_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 450 9 9, g32p_row19_traceSegment_099_0450_0009, g32p_row19_traceSegment_099_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 432 18 18, g32p_row19_traceSegment_099_0432_0018, g32p_row19_traceSegment_099_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 468 9 9, g32p_row19_traceSegment_099_0468_0009, g32p_row19_traceSegment_099_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 486 9 9, g32p_row19_traceSegment_099_0486_0009, g32p_row19_traceSegment_099_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 468 18 18, g32p_row19_traceSegment_099_0468_0018, g32p_row19_traceSegment_099_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 432 36 36, g32p_row19_traceSegment_099_0432_0036, g32p_row19_traceSegment_099_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 504 9 9, g32p_row19_traceSegment_099_0504_0009, g32p_row19_traceSegment_099_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 522 9 9, g32p_row19_traceSegment_099_0522_0009, g32p_row19_traceSegment_099_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 504 18 18, g32p_row19_traceSegment_099_0504_0018, g32p_row19_traceSegment_099_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 540 9 9, g32p_row19_traceSegment_099_0540_0009, g32p_row19_traceSegment_099_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 558 9 9, g32p_row19_traceSegment_099_0558_0009, g32p_row19_traceSegment_099_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 540 18 18, g32p_row19_traceSegment_099_0540_0018, g32p_row19_traceSegment_099_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 504 36 36, g32p_row19_traceSegment_099_0504_0036, g32p_row19_traceSegment_099_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 432 72 72, g32p_row19_traceSegment_099_0432_0072, g32p_row19_traceSegment_099_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_099 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 288 144 144, g32p_row19_traceSegment_099_0288_0144, g32p_row19_traceSegment_099_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_099 0 576 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 288 288, g32p_row19_traceSegment_099_0000_0288, g32p_row19_traceSegment_099_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 576 9 9, g32p_row19_traceSegment_099_0576_0009, g32p_row19_traceSegment_099_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 594 9 9, g32p_row19_traceSegment_099_0594_0009, g32p_row19_traceSegment_099_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 576 18 18, g32p_row19_traceSegment_099_0576_0018, g32p_row19_traceSegment_099_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 612 9 9, g32p_row19_traceSegment_099_0612_0009, g32p_row19_traceSegment_099_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 630 9 9, g32p_row19_traceSegment_099_0630_0009, g32p_row19_traceSegment_099_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 612 18 18, g32p_row19_traceSegment_099_0612_0018, g32p_row19_traceSegment_099_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 576 36 36, g32p_row19_traceSegment_099_0576_0036, g32p_row19_traceSegment_099_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 648 9 9, g32p_row19_traceSegment_099_0648_0009, g32p_row19_traceSegment_099_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 666 9 9, g32p_row19_traceSegment_099_0666_0009, g32p_row19_traceSegment_099_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 648 18 18, g32p_row19_traceSegment_099_0648_0018, g32p_row19_traceSegment_099_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 684 9 9, g32p_row19_traceSegment_099_0684_0009, g32p_row19_traceSegment_099_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 702 9 9, g32p_row19_traceSegment_099_0702_0009, g32p_row19_traceSegment_099_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 684 18 18, g32p_row19_traceSegment_099_0684_0018, g32p_row19_traceSegment_099_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 648 36 36, g32p_row19_traceSegment_099_0648_0036, g32p_row19_traceSegment_099_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 576 72 72, g32p_row19_traceSegment_099_0576_0072, g32p_row19_traceSegment_099_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 720 9 9, g32p_row19_traceSegment_099_0720_0009, g32p_row19_traceSegment_099_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 738 9 9, g32p_row19_traceSegment_099_0738_0009, g32p_row19_traceSegment_099_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 720 18 18, g32p_row19_traceSegment_099_0720_0018, g32p_row19_traceSegment_099_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 756 9 9, g32p_row19_traceSegment_099_0756_0009, g32p_row19_traceSegment_099_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 774 9 9, g32p_row19_traceSegment_099_0774_0009, g32p_row19_traceSegment_099_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 756 18 18, g32p_row19_traceSegment_099_0756_0018, g32p_row19_traceSegment_099_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 720 36 36, g32p_row19_traceSegment_099_0720_0036, g32p_row19_traceSegment_099_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 792 9 9, g32p_row19_traceSegment_099_0792_0009, g32p_row19_traceSegment_099_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 810 9 9, g32p_row19_traceSegment_099_0810_0009, g32p_row19_traceSegment_099_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 792 18 18, g32p_row19_traceSegment_099_0792_0018, g32p_row19_traceSegment_099_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 828 9 9, g32p_row19_traceSegment_099_0828_0009, g32p_row19_traceSegment_099_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 846 9 9, g32p_row19_traceSegment_099_0846_0009, g32p_row19_traceSegment_099_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 828 18 18, g32p_row19_traceSegment_099_0828_0018, g32p_row19_traceSegment_099_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 792 36 36, g32p_row19_traceSegment_099_0792_0036, g32p_row19_traceSegment_099_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 720 72 72, g32p_row19_traceSegment_099_0720_0072, g32p_row19_traceSegment_099_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_099 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 576 144 144, g32p_row19_traceSegment_099_0576_0144, g32p_row19_traceSegment_099_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 864 9 9, g32p_row19_traceSegment_099_0864_0009, g32p_row19_traceSegment_099_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 882 9 9, g32p_row19_traceSegment_099_0882_0009, g32p_row19_traceSegment_099_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 864 18 18, g32p_row19_traceSegment_099_0864_0018, g32p_row19_traceSegment_099_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 900 9 9, g32p_row19_traceSegment_099_0900_0009, g32p_row19_traceSegment_099_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 918 9 9, g32p_row19_traceSegment_099_0918_0009, g32p_row19_traceSegment_099_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 900 18 18, g32p_row19_traceSegment_099_0900_0018, g32p_row19_traceSegment_099_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 864 36 36, g32p_row19_traceSegment_099_0864_0036, g32p_row19_traceSegment_099_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 936 9 9, g32p_row19_traceSegment_099_0936_0009, g32p_row19_traceSegment_099_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 954 9 9, g32p_row19_traceSegment_099_0954_0009, g32p_row19_traceSegment_099_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 936 18 18, g32p_row19_traceSegment_099_0936_0018, g32p_row19_traceSegment_099_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 972 9 9, g32p_row19_traceSegment_099_0972_0009, g32p_row19_traceSegment_099_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 990 9 9, g32p_row19_traceSegment_099_0990_0009, g32p_row19_traceSegment_099_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 972 18 18, g32p_row19_traceSegment_099_0972_0018, g32p_row19_traceSegment_099_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 936 36 36, g32p_row19_traceSegment_099_0936_0036, g32p_row19_traceSegment_099_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 864 72 72, g32p_row19_traceSegment_099_0864_0072, g32p_row19_traceSegment_099_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1008 9 9, g32p_row19_traceSegment_099_1008_0009, g32p_row19_traceSegment_099_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1026 9 9, g32p_row19_traceSegment_099_1026_0009, g32p_row19_traceSegment_099_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1008 18 18, g32p_row19_traceSegment_099_1008_0018, g32p_row19_traceSegment_099_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1044 9 9, g32p_row19_traceSegment_099_1044_0009, g32p_row19_traceSegment_099_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1062 9 9, g32p_row19_traceSegment_099_1062_0009, g32p_row19_traceSegment_099_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1044 18 18, g32p_row19_traceSegment_099_1044_0018, g32p_row19_traceSegment_099_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1008 36 36, g32p_row19_traceSegment_099_1008_0036, g32p_row19_traceSegment_099_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1080 9 9, g32p_row19_traceSegment_099_1080_0009, g32p_row19_traceSegment_099_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1098 9 9, g32p_row19_traceSegment_099_1098_0009, g32p_row19_traceSegment_099_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1080 18 18, g32p_row19_traceSegment_099_1080_0018, g32p_row19_traceSegment_099_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1116 9 9, g32p_row19_traceSegment_099_1116_0009, g32p_row19_traceSegment_099_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_099 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_099_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_099 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1134 9 9, g32p_row19_traceSegment_099_1134_0009, g32p_row19_traceSegment_099_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_099 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1116 18 18, g32p_row19_traceSegment_099_1116_0018, g32p_row19_traceSegment_099_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_099 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1080 36 36, g32p_row19_traceSegment_099_1080_0036, g32p_row19_traceSegment_099_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_099_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_099 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 1008 72 72, g32p_row19_traceSegment_099_1008_0072, g32p_row19_traceSegment_099_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_099 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 864 144 144, g32p_row19_traceSegment_099_0864_0144, g32p_row19_traceSegment_099_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_099 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 576 288 288, g32p_row19_traceSegment_099_0576_0288, g32p_row19_traceSegment_099_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_099_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_099 0 1152 = [1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_099 0 576 576, g32p_row19_traceSegment_099_0000_0576, g32p_row19_traceSegment_099_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_099_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row19_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row19_supplierClassifier (Fin.ofNat 1152 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row19_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row19_traceSegment_101_0000_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 0 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0009_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 9 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 9 9, g32p_row19_traceSegment_101_0000_0009, g32p_row19_traceSegment_101_0009_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0018_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 18 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0027_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 27 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0018_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 18 9 9, g32p_row19_traceSegment_101_0018_0009, g32p_row19_traceSegment_101_0027_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 18 18, g32p_row19_traceSegment_101_0000_0018, g32p_row19_traceSegment_101_0018_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0036_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 36 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0045_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 45 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0036_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 36 9 9, g32p_row19_traceSegment_101_0036_0009, g32p_row19_traceSegment_101_0045_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0054_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 54 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0063_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 63 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0054_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 54 9 9, g32p_row19_traceSegment_101_0054_0009, g32p_row19_traceSegment_101_0063_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0036_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 36 18 18, g32p_row19_traceSegment_101_0036_0018, g32p_row19_traceSegment_101_0054_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 36 36, g32p_row19_traceSegment_101_0000_0036, g32p_row19_traceSegment_101_0036_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0072_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 72 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0081_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 81 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0072_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 72 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 72 9 9, g32p_row19_traceSegment_101_0072_0009, g32p_row19_traceSegment_101_0081_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0090_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 90 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0099_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 99 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0090_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 90 9 9, g32p_row19_traceSegment_101_0090_0009, g32p_row19_traceSegment_101_0099_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0072_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 72 18 18, g32p_row19_traceSegment_101_0072_0018, g32p_row19_traceSegment_101_0090_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0108_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 108 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0117_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 117 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0108_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 108 9 9, g32p_row19_traceSegment_101_0108_0009, g32p_row19_traceSegment_101_0117_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0126_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 126 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0135_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 135 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0126_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 126 9 9, g32p_row19_traceSegment_101_0126_0009, g32p_row19_traceSegment_101_0135_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0108_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 108 18 18, g32p_row19_traceSegment_101_0108_0018, g32p_row19_traceSegment_101_0126_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0072_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 72 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 72 36 36, g32p_row19_traceSegment_101_0072_0036, g32p_row19_traceSegment_101_0108_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 72 72, g32p_row19_traceSegment_101_0000_0072, g32p_row19_traceSegment_101_0072_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0144_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 144 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0153_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 153 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0144_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 144 9 9, g32p_row19_traceSegment_101_0144_0009, g32p_row19_traceSegment_101_0153_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0162_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 162 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0171_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 171 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0162_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 162 9 9, g32p_row19_traceSegment_101_0162_0009, g32p_row19_traceSegment_101_0171_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0144_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 144 18 18, g32p_row19_traceSegment_101_0144_0018, g32p_row19_traceSegment_101_0162_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0180_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 180 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0189_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 189 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0180_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 180 9 9, g32p_row19_traceSegment_101_0180_0009, g32p_row19_traceSegment_101_0189_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0198_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 198 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0207_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 207 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0198_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 198 9 9, g32p_row19_traceSegment_101_0198_0009, g32p_row19_traceSegment_101_0207_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0180_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 180 18 18, g32p_row19_traceSegment_101_0180_0018, g32p_row19_traceSegment_101_0198_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0144_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 144 36 36, g32p_row19_traceSegment_101_0144_0036, g32p_row19_traceSegment_101_0180_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0216_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 216 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0225_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 225 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0216_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 216 9 9, g32p_row19_traceSegment_101_0216_0009, g32p_row19_traceSegment_101_0225_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0234_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 234 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0243_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 243 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0234_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 234 9 9, g32p_row19_traceSegment_101_0234_0009, g32p_row19_traceSegment_101_0243_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0216_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 216 18 18, g32p_row19_traceSegment_101_0216_0018, g32p_row19_traceSegment_101_0234_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0252_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 252 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0261_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 261 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0252_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 252 9 9, g32p_row19_traceSegment_101_0252_0009, g32p_row19_traceSegment_101_0261_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0270_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 270 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0279_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 279 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0270_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 270 9 9, g32p_row19_traceSegment_101_0270_0009, g32p_row19_traceSegment_101_0279_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0252_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 252 18 18, g32p_row19_traceSegment_101_0252_0018, g32p_row19_traceSegment_101_0270_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0216_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 216 36 36, g32p_row19_traceSegment_101_0216_0036, g32p_row19_traceSegment_101_0252_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0144_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 144 72 72, g32p_row19_traceSegment_101_0144_0072, g32p_row19_traceSegment_101_0216_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_0288 : g32p_coeffSegment g32p_row19_traceSegment_101 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 144 144, g32p_row19_traceSegment_101_0000_0144, g32p_row19_traceSegment_101_0144_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0288_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 288 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0297_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 297 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0288_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 288 9 9, g32p_row19_traceSegment_101_0288_0009, g32p_row19_traceSegment_101_0297_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0306_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 306 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0315_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 315 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0306_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 306 9 9, g32p_row19_traceSegment_101_0306_0009, g32p_row19_traceSegment_101_0315_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0288_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 288 18 18, g32p_row19_traceSegment_101_0288_0018, g32p_row19_traceSegment_101_0306_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0324_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 324 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0333_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 333 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0324_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 324 9 9, g32p_row19_traceSegment_101_0324_0009, g32p_row19_traceSegment_101_0333_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0342_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 342 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0351_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 351 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0342_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 342 9 9, g32p_row19_traceSegment_101_0342_0009, g32p_row19_traceSegment_101_0351_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0324_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 324 18 18, g32p_row19_traceSegment_101_0324_0018, g32p_row19_traceSegment_101_0342_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0288_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 288 36 36, g32p_row19_traceSegment_101_0288_0036, g32p_row19_traceSegment_101_0324_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0360_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 360 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0369_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 369 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0360_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 360 9 9, g32p_row19_traceSegment_101_0360_0009, g32p_row19_traceSegment_101_0369_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0378_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 378 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0387_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 387 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0378_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 378 9 9, g32p_row19_traceSegment_101_0378_0009, g32p_row19_traceSegment_101_0387_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0360_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 360 18 18, g32p_row19_traceSegment_101_0360_0018, g32p_row19_traceSegment_101_0378_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0396_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 396 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0405_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 405 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0396_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 396 9 9, g32p_row19_traceSegment_101_0396_0009, g32p_row19_traceSegment_101_0405_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0414_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 414 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0423_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 423 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0414_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 414 9 9, g32p_row19_traceSegment_101_0414_0009, g32p_row19_traceSegment_101_0423_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0396_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 396 18 18, g32p_row19_traceSegment_101_0396_0018, g32p_row19_traceSegment_101_0414_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0360_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 360 36 36, g32p_row19_traceSegment_101_0360_0036, g32p_row19_traceSegment_101_0396_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0288_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 288 72 72, g32p_row19_traceSegment_101_0288_0072, g32p_row19_traceSegment_101_0360_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0432_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 432 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0441_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 441 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0432_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 432 9 9, g32p_row19_traceSegment_101_0432_0009, g32p_row19_traceSegment_101_0441_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0450_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 450 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0459_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 459 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0450_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 450 9 9, g32p_row19_traceSegment_101_0450_0009, g32p_row19_traceSegment_101_0459_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0432_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 432 18 18, g32p_row19_traceSegment_101_0432_0018, g32p_row19_traceSegment_101_0450_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0468_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 468 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0477_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 477 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0468_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 468 9 9, g32p_row19_traceSegment_101_0468_0009, g32p_row19_traceSegment_101_0477_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0486_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 486 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0495_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 495 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0486_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 486 9 9, g32p_row19_traceSegment_101_0486_0009, g32p_row19_traceSegment_101_0495_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0468_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 468 18 18, g32p_row19_traceSegment_101_0468_0018, g32p_row19_traceSegment_101_0486_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0432_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 432 36 36, g32p_row19_traceSegment_101_0432_0036, g32p_row19_traceSegment_101_0468_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0504_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 504 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0513_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 513 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0504_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 504 9 9, g32p_row19_traceSegment_101_0504_0009, g32p_row19_traceSegment_101_0513_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0522_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 522 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0531_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 531 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0522_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 522 9 9, g32p_row19_traceSegment_101_0522_0009, g32p_row19_traceSegment_101_0531_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0504_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 504 18 18, g32p_row19_traceSegment_101_0504_0018, g32p_row19_traceSegment_101_0522_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0540_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 540 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0549_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 549 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0540_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 540 9 9, g32p_row19_traceSegment_101_0540_0009, g32p_row19_traceSegment_101_0549_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0558_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 558 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0567_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 567 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0558_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 558 9 9, g32p_row19_traceSegment_101_0558_0009, g32p_row19_traceSegment_101_0567_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0540_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 540 18 18, g32p_row19_traceSegment_101_0540_0018, g32p_row19_traceSegment_101_0558_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0504_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 504 36 36, g32p_row19_traceSegment_101_0504_0036, g32p_row19_traceSegment_101_0540_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0432_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 432 72 72, g32p_row19_traceSegment_101_0432_0072, g32p_row19_traceSegment_101_0504_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0288_0288 : g32p_coeffSegment g32p_row19_traceSegment_101 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 288 144 144, g32p_row19_traceSegment_101_0288_0144, g32p_row19_traceSegment_101_0432_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_0576 : g32p_coeffSegment g32p_row19_traceSegment_101 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 288 288, g32p_row19_traceSegment_101_0000_0288, g32p_row19_traceSegment_101_0288_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 576 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0585_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 585 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 576 9 9, g32p_row19_traceSegment_101_0576_0009, g32p_row19_traceSegment_101_0585_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0594_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 594 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0603_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 603 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0594_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 594 9 9, g32p_row19_traceSegment_101_0594_0009, g32p_row19_traceSegment_101_0603_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 576 18 18, g32p_row19_traceSegment_101_0576_0018, g32p_row19_traceSegment_101_0594_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0612_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 612 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0621_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 621 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0612_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 612 9 9, g32p_row19_traceSegment_101_0612_0009, g32p_row19_traceSegment_101_0621_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0630_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 630 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0639_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 639 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0630_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 630 9 9, g32p_row19_traceSegment_101_0630_0009, g32p_row19_traceSegment_101_0639_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0612_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 612 18 18, g32p_row19_traceSegment_101_0612_0018, g32p_row19_traceSegment_101_0630_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 576 36 36, g32p_row19_traceSegment_101_0576_0036, g32p_row19_traceSegment_101_0612_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0648_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 648 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0657_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 657 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0648_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 648 9 9, g32p_row19_traceSegment_101_0648_0009, g32p_row19_traceSegment_101_0657_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0666_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 666 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0675_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 675 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0666_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 666 9 9, g32p_row19_traceSegment_101_0666_0009, g32p_row19_traceSegment_101_0675_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0648_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 648 18 18, g32p_row19_traceSegment_101_0648_0018, g32p_row19_traceSegment_101_0666_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0684_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 684 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0693_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 693 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0684_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 684 9 9, g32p_row19_traceSegment_101_0684_0009, g32p_row19_traceSegment_101_0693_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0702_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 702 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0711_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 711 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0702_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 702 9 9, g32p_row19_traceSegment_101_0702_0009, g32p_row19_traceSegment_101_0711_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0684_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 684 18 18, g32p_row19_traceSegment_101_0684_0018, g32p_row19_traceSegment_101_0702_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0648_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 648 36 36, g32p_row19_traceSegment_101_0648_0036, g32p_row19_traceSegment_101_0684_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 576 72 72, g32p_row19_traceSegment_101_0576_0072, g32p_row19_traceSegment_101_0648_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0720_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 720 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0729_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 729 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0720_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 720 9 9, g32p_row19_traceSegment_101_0720_0009, g32p_row19_traceSegment_101_0729_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0738_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 738 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0747_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 747 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0738_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 738 9 9, g32p_row19_traceSegment_101_0738_0009, g32p_row19_traceSegment_101_0747_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0720_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 720 18 18, g32p_row19_traceSegment_101_0720_0018, g32p_row19_traceSegment_101_0738_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0756_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 756 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0765_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 765 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0756_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 756 9 9, g32p_row19_traceSegment_101_0756_0009, g32p_row19_traceSegment_101_0765_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0774_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 774 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0783_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 783 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0774_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 774 9 9, g32p_row19_traceSegment_101_0774_0009, g32p_row19_traceSegment_101_0783_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0756_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 756 18 18, g32p_row19_traceSegment_101_0756_0018, g32p_row19_traceSegment_101_0774_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0720_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 720 36 36, g32p_row19_traceSegment_101_0720_0036, g32p_row19_traceSegment_101_0756_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0792_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 792 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0801_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 801 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0792_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 792 9 9, g32p_row19_traceSegment_101_0792_0009, g32p_row19_traceSegment_101_0801_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0810_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 810 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0819_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 819 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0810_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 810 9 9, g32p_row19_traceSegment_101_0810_0009, g32p_row19_traceSegment_101_0819_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0792_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 792 18 18, g32p_row19_traceSegment_101_0792_0018, g32p_row19_traceSegment_101_0810_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0828_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 828 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0837_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 837 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0828_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 828 9 9, g32p_row19_traceSegment_101_0828_0009, g32p_row19_traceSegment_101_0837_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0846_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 846 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0855_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 855 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0846_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 846 9 9, g32p_row19_traceSegment_101_0846_0009, g32p_row19_traceSegment_101_0855_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0828_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 828 18 18, g32p_row19_traceSegment_101_0828_0018, g32p_row19_traceSegment_101_0846_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0792_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 792 36 36, g32p_row19_traceSegment_101_0792_0036, g32p_row19_traceSegment_101_0828_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0720_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 720 72 72, g32p_row19_traceSegment_101_0720_0072, g32p_row19_traceSegment_101_0792_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0288 : g32p_coeffSegment g32p_row19_traceSegment_101 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 576 144 144, g32p_row19_traceSegment_101_0576_0144, g32p_row19_traceSegment_101_0720_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0864_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 864 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0873_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 873 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0864_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 864 9 9, g32p_row19_traceSegment_101_0864_0009, g32p_row19_traceSegment_101_0873_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0882_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 882 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0891_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 891 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0882_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 882 9 9, g32p_row19_traceSegment_101_0882_0009, g32p_row19_traceSegment_101_0891_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0864_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 864 18 18, g32p_row19_traceSegment_101_0864_0018, g32p_row19_traceSegment_101_0882_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0900_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 900 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0909_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 909 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0900_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 900 9 9, g32p_row19_traceSegment_101_0900_0009, g32p_row19_traceSegment_101_0909_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0918_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 918 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0927_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 927 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0918_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 918 9 9, g32p_row19_traceSegment_101_0918_0009, g32p_row19_traceSegment_101_0927_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0900_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 900 18 18, g32p_row19_traceSegment_101_0900_0018, g32p_row19_traceSegment_101_0918_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0864_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 864 36 36, g32p_row19_traceSegment_101_0864_0036, g32p_row19_traceSegment_101_0900_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0936_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 936 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0945_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 945 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0936_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 936 9 9, g32p_row19_traceSegment_101_0936_0009, g32p_row19_traceSegment_101_0945_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0954_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 954 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0963_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 963 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0954_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 954 9 9, g32p_row19_traceSegment_101_0954_0009, g32p_row19_traceSegment_101_0963_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0936_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 936 18 18, g32p_row19_traceSegment_101_0936_0018, g32p_row19_traceSegment_101_0954_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0972_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 972 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0981_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 981 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0972_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 972 9 9, g32p_row19_traceSegment_101_0972_0009, g32p_row19_traceSegment_101_0981_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0990_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 990 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0999_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 999 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_0990_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 990 9 9, g32p_row19_traceSegment_101_0990_0009, g32p_row19_traceSegment_101_0999_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0972_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 972 18 18, g32p_row19_traceSegment_101_0972_0018, g32p_row19_traceSegment_101_0990_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0936_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 936 36 36, g32p_row19_traceSegment_101_0936_0036, g32p_row19_traceSegment_101_0972_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0864_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 864 72 72, g32p_row19_traceSegment_101_0864_0072, g32p_row19_traceSegment_101_0936_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1008_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1008 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1017_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1017 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1008_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1008 9 9, g32p_row19_traceSegment_101_1008_0009, g32p_row19_traceSegment_101_1017_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1026_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1026 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1035_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1035 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1026_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1026 9 9, g32p_row19_traceSegment_101_1026_0009, g32p_row19_traceSegment_101_1035_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1008_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1008 18 18, g32p_row19_traceSegment_101_1008_0018, g32p_row19_traceSegment_101_1026_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1044_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1044 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1053_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1053 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1044_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1044 9 9, g32p_row19_traceSegment_101_1044_0009, g32p_row19_traceSegment_101_1053_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1062_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1062 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1071_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1071 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1062_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1062 9 9, g32p_row19_traceSegment_101_1062_0009, g32p_row19_traceSegment_101_1071_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1044_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1044 18 18, g32p_row19_traceSegment_101_1044_0018, g32p_row19_traceSegment_101_1062_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1008_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1008 36 36, g32p_row19_traceSegment_101_1008_0036, g32p_row19_traceSegment_101_1044_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1080_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1080 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1089_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1089 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1080_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1080 9 9, g32p_row19_traceSegment_101_1080_0009, g32p_row19_traceSegment_101_1089_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1098_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1098 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1107_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1107 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1098_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1098 9 9, g32p_row19_traceSegment_101_1098_0009, g32p_row19_traceSegment_101_1107_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1080_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1080 18 18, g32p_row19_traceSegment_101_1080_0018, g32p_row19_traceSegment_101_1098_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1116_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1116 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1125_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1125 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1116_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1116 9 9, g32p_row19_traceSegment_101_1116_0009, g32p_row19_traceSegment_101_1125_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1134_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1134 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1143_0009 : g32p_coeffSegment g32p_row19_traceSegment_101 1143 9 = [] := by
  decide +kernel

private theorem g32p_row19_traceSegment_101_1134_0018 : g32p_coeffSegment g32p_row19_traceSegment_101 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1134 9 9, g32p_row19_traceSegment_101_1134_0009, g32p_row19_traceSegment_101_1143_0009]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1116_0036 : g32p_coeffSegment g32p_row19_traceSegment_101 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1116 18 18, g32p_row19_traceSegment_101_1116_0018, g32p_row19_traceSegment_101_1134_0018]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1080_0072 : g32p_coeffSegment g32p_row19_traceSegment_101 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1080 36 36, g32p_row19_traceSegment_101_1080_0036, g32p_row19_traceSegment_101_1116_0036]
  decide +kernel

private theorem g32p_row19_traceSegment_101_1008_0144 : g32p_coeffSegment g32p_row19_traceSegment_101 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 1008 72 72, g32p_row19_traceSegment_101_1008_0072, g32p_row19_traceSegment_101_1080_0072]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0864_0288 : g32p_coeffSegment g32p_row19_traceSegment_101 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 864 144 144, g32p_row19_traceSegment_101_0864_0144, g32p_row19_traceSegment_101_1008_0144]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0576_0576 : g32p_coeffSegment g32p_row19_traceSegment_101 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 576 288 288, g32p_row19_traceSegment_101_0576_0288, g32p_row19_traceSegment_101_0864_0288]
  decide +kernel

private theorem g32p_row19_traceSegment_101_0000_1152 : g32p_coeffSegment g32p_row19_traceSegment_101 0 1152 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row19_traceSegment_101 0 576 576, g32p_row19_traceSegment_101_0000_0576, g32p_row19_traceSegment_101_0576_0576]
  decide +kernel

theorem g32p_row19_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row19_traceSegment_101_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row19_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 96) (g32p_literalTraceValue 18 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_096]
  decide +kernel

theorem g32p_row19_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 97) (g32p_literalTraceValue 18 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_097]
  decide +kernel

theorem g32p_row19_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 99) (g32p_literalTraceValue 18 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row19_traceCoefficients_099]
  decide +kernel

theorem g32p_row19_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) 101) (g32p_literalTraceValue 18 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row19_traceCoefficients_101]
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

def g32p_row19_generatorIndex : Fin 8 → Fin 408 :=
  ![18, 69, 120, 171, 240, 241, 342, 343]

theorem g32p_row19_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup14_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 18 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 18 g32p_row19_supplierClass
    g32p_row19_supplierClass_isConj g32p_supplierGroup14_support g32p_row19_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row19_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup14_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row19_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 18 c false (g32p_row19_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 18 c true (g32p_row19_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 18 c false (g32p_row19_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 18 c true (g32p_row19_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 18 c false (g32p_row19_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 18 c false (g32p_row19_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 18 c true (g32p_row19_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 18 c true (g32p_row19_coinduced_zero c hc true) 3

theorem g32p_row19_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup14_support →
      g32p_literalTraceValue (g32p_row19_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row19_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup14_support) :
    g32p_literalTraceValue (g32p_row19_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup14_support →
    g32p_literalTraceValue (g32p_row19_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row19_zeroTrace_block_00 r k
  · exact g32p_row19_zeroTrace_block_01 r k
  · exact g32p_row19_zeroTrace_block_02 r k
  · exact g32p_row19_zeroTrace_block_03 r k
  · exact g32p_row19_zeroTrace_block_04 r k
  · exact g32p_row19_zeroTrace_block_05 r k
  · exact g32p_row19_zeroTrace_block_06 r k

theorem g32p_row19_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup14_support) :
    (g32p_recordedInductionGenerators (g32p_row19_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row19_generatorIndex k) c) := by
  rw [g32p_row19_recordedGenerator_zero c hc k, g32p_row19_zeroTrace_arithmetic c k hc]
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

def g32p_row19_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [10368, 10368, 10368])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 2304, 2304] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [13824, 13824] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [-1152, 0, 1152, 1152] else []) else (if i.val < 24 then [] else [10368, 10368, 10368]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [-3456] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [0, 0, 3456, 3456] else [1152, 1152, 1152, 1152]))) else (if i.val < 34 then (if i.val < 32 then [3456, 3456, 3456] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [8064, 10368, 10368] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [1152, 1152] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [-3456]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [0, 1152])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 1152, 1152] else [6912, 6912, 3456])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [10368, 10368, 10368]))) else (if i.val < 60 then (if i.val < 58 then [-1152] else (if i.val < 59 then [] else [3456, 3456])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [-10368, 3456, 3456])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [2304, 2304] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [3456, 3456, 6912, 3456] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [10368, 10368, 10368])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 13824, 13824] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [3456, 3456, 3456] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row19_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup14_support) :
    g32p_supplierTracePolynomialCheck 1152 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) c) (g32p_literalTraceValue 18 c)
      [1, -1, 1] (g32p_row19_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row19_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_004
  · exact g32p_row19_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_024
  · exact g32p_row19_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_029
  · exact g32p_row19_tracePolynomial_030
  · exact g32p_row19_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_037
  · exact g32p_row19_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_049
  · exact g32p_row19_tracePolynomial_050
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_056
  · exact g32p_row19_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_082
  · exact g32p_row19_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_096
  · exact g32p_row19_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup14_support) hc)
  · exact g32p_row19_tracePolynomial_101

theorem g32p_row19_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 18 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 18 c) := by
  by_cases hc : c ∈ g32p_supplierGroup14_support
  · have hclass (j : Fin 1152) :
        IsConj (g32p_literalRepresentative c) (g32p_row19_groupEquiv j : g32p_G) ↔
          g32p_row19_supplierClassifier j = c := by
      simpa only [g32p_row19_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row19_supplierClass_iff (g32p_row19_groupEquiv j) c
    have hχ (j : Fin 1152) :
        (g32p_recordedSupplierCharacters 18 (g32p_row19_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row19_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 18 (show (g32p_recordedSuppliers 18).H from g32p_row19_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row19_characterValues (g32p_row19_groupEquiv.symm (g32p_row19_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 18).H (g32p_recordedSupplierCharacters 18)
      (g32p_literalRepresentative c) g32p_row19_groupEquiv g32p_row19_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row19_characterValues j)).val) c 6 1152
      (g32p_literalCentralizer c) (g32p_literalTraceValue 18 c) [1, -1, 1]
      (g32p_row19_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row19_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 18)))
      (g32p_row19_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row19_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row19_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row19_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
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

theorem g32p_row19_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_0 r
  · exact g32p_row19_variantArithmetic_01_0 r
  · exact g32p_row19_variantArithmetic_02_0 r
  · exact g32p_row19_variantArithmetic_03_0 r
  · exact g32p_row19_variantArithmetic_04_0 r
  · exact g32p_row19_variantArithmetic_05_0 r
  · exact g32p_row19_variantArithmetic_06_0 r

theorem g32p_row19_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_1 r
  · exact g32p_row19_variantArithmetic_01_1 r
  · exact g32p_row19_variantArithmetic_02_1 r
  · exact g32p_row19_variantArithmetic_03_1 r
  · exact g32p_row19_variantArithmetic_04_1 r
  · exact g32p_row19_variantArithmetic_05_1 r
  · exact g32p_row19_variantArithmetic_06_1 r

theorem g32p_row19_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_2 r
  · exact g32p_row19_variantArithmetic_01_2 r
  · exact g32p_row19_variantArithmetic_02_2 r
  · exact g32p_row19_variantArithmetic_03_2 r
  · exact g32p_row19_variantArithmetic_04_2 r
  · exact g32p_row19_variantArithmetic_05_2 r
  · exact g32p_row19_variantArithmetic_06_2 r

theorem g32p_row19_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_3 r
  · exact g32p_row19_variantArithmetic_01_3 r
  · exact g32p_row19_variantArithmetic_02_3 r
  · exact g32p_row19_variantArithmetic_03_3 r
  · exact g32p_row19_variantArithmetic_04_3 r
  · exact g32p_row19_variantArithmetic_05_3 r
  · exact g32p_row19_variantArithmetic_06_3 r

theorem g32p_row19_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_4 r
  · exact g32p_row19_variantArithmetic_01_4 r
  · exact g32p_row19_variantArithmetic_02_4 r
  · exact g32p_row19_variantArithmetic_03_4 r
  · exact g32p_row19_variantArithmetic_04_4 r
  · exact g32p_row19_variantArithmetic_05_4 r
  · exact g32p_row19_variantArithmetic_06_4 r

theorem g32p_row19_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_5 r
  · exact g32p_row19_variantArithmetic_01_5 r
  · exact g32p_row19_variantArithmetic_02_5 r
  · exact g32p_row19_variantArithmetic_03_5 r
  · exact g32p_row19_variantArithmetic_04_5 r
  · exact g32p_row19_variantArithmetic_05_5 r
  · exact g32p_row19_variantArithmetic_06_5 r

theorem g32p_row19_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_6 r
  · exact g32p_row19_variantArithmetic_01_6 r
  · exact g32p_row19_variantArithmetic_02_6 r
  · exact g32p_row19_variantArithmetic_03_6 r
  · exact g32p_row19_variantArithmetic_04_6 r
  · exact g32p_row19_variantArithmetic_05_6 r
  · exact g32p_row19_variantArithmetic_06_6 r

theorem g32p_row19_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row19_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 18 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row19_variantArithmetic_00_7 r
  · exact g32p_row19_variantArithmetic_01_7 r
  · exact g32p_row19_variantArithmetic_02_7 r
  · exact g32p_row19_variantArithmetic_03_7 r
  · exact g32p_row19_variantArithmetic_04_7 r
  · exact g32p_row19_variantArithmetic_05_7 r
  · exact g32p_row19_variantArithmetic_06_7 r

theorem g32p_row19_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row19_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row19_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 18 c _ (g32p_row19_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row19_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup15_source : Fin 144 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (73, 75)) else (if i.val < 3 then (19, 12) else (14, 225))) else (if i.val < 6 then (if i.val < 5 then (0, 99) else (3, 181)) else (if i.val < 7 then (83, 94) else (if i.val < 8 then (127, 202) else (47, 18))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (53, 47) else (72, 86)) else (if i.val < 12 then (108, 115) else (28, 133))) else (if i.val < 15 then (if i.val < 14 then (13, 150) else (33, 221)) else (if i.val < 16 then (66, 231) else (if i.val < 17 then (69, 236) else (117, 230)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (51, 28) else (130, 166)) else (if i.val < 21 then (107, 55) else (60, 20))) else (if i.val < 24 then (if i.val < 23 then (86, 160) else (143, 33)) else (if i.val < 25 then (115, 113) else (if i.val < 26 then (103, 130) else (114, 68))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (94, 171) else (56, 127)) else (if i.val < 30 then (111, 183) else (12, 84))) else (if i.val < 33 then (if i.val < 32 then (102, 102) else (132, 12)) else (if i.val < 34 then (49, 102) else (if i.val < 35 then (0, 96) else (18, 254))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (83, 186) else (109, 244)) else (if i.val < 39 then (50, 130) else (125, 170))) else (if i.val < 42 then (if i.val < 41 then (102, 44) else (55, 180)) else (if i.val < 43 then (52, 252) else (if i.val < 44 then (54, 126) else (89, 225))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (23, 223) else (124, 86)) else (if i.val < 48 then (118, 19) else (15, 108))) else (if i.val < 51 then (if i.val < 50 then (85, 182) else (98, 178)) else (if i.val < 52 then (82, 250) else (if i.val < 53 then (4, 179) else (120, 57)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (38, 249) else (91, 194)) else (if i.val < 57 then (110, 220) else (0, 101))) else (if i.val < 60 then (if i.val < 59 then (110, 246) else (118, 150)) else (if i.val < 61 then (56, 177) else (if i.val < 62 then (1, 197) else (130, 187))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (109, 93) else (2, 52)) else (if i.val < 66 then (0, 97) else (81, 73))) else (if i.val < 69 then (if i.val < 68 then (27, 72) else (28, 50)) else (if i.val < 70 then (132, 232) else (if i.val < 71 then (45, 114) else (95, 93)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (127, 180) else (129, 221)) else (if i.val < 75 then (105, 44) else (5, 245))) else (if i.val < 78 then (if i.val < 77 then (103, 188) else (3, 42)) else (if i.val < 79 then (2, 129) else (if i.val < 80 then (120, 61) else (127, 210))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (112, 223) else (89, 117)) else (if i.val < 84 then (96, 231) else (123, 43))) else (if i.val < 87 then (if i.val < 86 then (107, 125) else (104, 84)) else (if i.val < 88 then (139, 110) else (if i.val < 89 then (12, 140) else (123, 7)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (10, 177) else (38, 117)) else (if i.val < 93 then (68, 65) else (0, 37))) else (if i.val < 96 then (if i.val < 95 then (112, 39) else (99, 38)) else (if i.val < 97 then (56, 141) else (if i.val < 98 then (114, 6) else (41, 92))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (85, 99) else (5, 38)) else (if i.val < 102 then (71, 49) else (86, 71))) else (if i.val < 105 then (if i.val < 104 then (104, 150) else (127, 197)) else (if i.val < 106 then (100, 230) else (if i.val < 107 then (102, 20) else (135, 221))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (135, 26) else (9, 228)) else (if i.val < 111 then (127, 145) else (51, 57))) else (if i.val < 114 then (if i.val < 113 then (55, 183) else (129, 15)) else (if i.val < 115 then (120, 193) else (if i.val < 116 then (54, 159) else (94, 55))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (140, 35) else (12, 133)) else (if i.val < 120 then (117, 222) else (76, 122))) else (if i.val < 123 then (if i.val < 122 then (130, 228) else (1, 255)) else (if i.val < 124 then (29, 193) else (if i.val < 125 then (79, 147) else (63, 211)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (100, 75) else (2, 205)) else (if i.val < 129 then (137, 187) else (58, 64))) else (if i.val < 132 then (if i.val < 131 then (89, 128) else (72, 125)) else (if i.val < 133 then (141, 153) else (if i.val < 134 then (117, 228) else (27, 243))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (79, 132) else (46, 208)) else (if i.val < 138 then (136, 54) else (135, 23))) else (if i.val < 141 then (if i.val < 140 then (14, 174) else (20, 141)) else (if i.val < 142 then (134, 191) else (if i.val < 143 then (99, 49) else (89, 114)))))))))

def g32p_supplierGroup15_classify : Fin 144 → Fin 102 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 52) else (if i.val < 3 then 31 else 100)) else (if i.val < 6 then (if i.val < 5 then 99 else 65) else (if i.val < 7 then 94 else (if i.val < 8 then 58 else 83)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 94 else 82) else (if i.val < 12 then 72 else 90)) else (if i.val < 15 then (if i.val < 14 then 87 else 28) else (if i.val < 16 then 5 else (if i.val < 17 then 83 else 23))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 65 else 83) else (if i.val < 21 then 90 else 27)) else (if i.val < 24 then (if i.val < 23 then 5 else 20) else (if i.val < 25 then 63 else (if i.val < 26 then 90 else 27)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 5 else 94) else (if i.val < 30 then 89 else 82)) else (if i.val < 33 then (if i.val < 32 then 80 else 7) else (if i.val < 34 then 88 else (if i.val < 35 then 96 else 31)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 55 else 94) else (if i.val < 39 then 31 else 63)) else (if i.val < 42 then (if i.val < 41 then 52 else 81) else (if i.val < 43 then 79 else (if i.val < 44 then 18 else 63)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 52 else 83) else (if i.val < 48 then 7 else 31)) else (if i.val < 51 then (if i.val < 50 then 17 else 55) else (if i.val < 52 then 41 else (if i.val < 53 then 83 else 7))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 31 else 17) else (if i.val < 57 then 55 else 101)) else (if i.val < 60 then (if i.val < 59 then 27 else 5) else (if i.val < 61 then 19 else (if i.val < 62 then 3 else 48)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 94 else 2) else (if i.val < 66 then 97 else 72)) else (if i.val < 69 then (if i.val < 68 then 90 else 61) else (if i.val < 70 then 27 else (if i.val < 71 then 52 else 72))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 90 else 41) else (if i.val < 75 then 58 else 8)) else (if i.val < 78 then (if i.val < 77 then 31 else 51) else (if i.val < 79 then 18 else (if i.val < 80 then 41 else 58)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 5 else 63) else (if i.val < 84 then 52 else 48)) else (if i.val < 87 then (if i.val < 86 then 72 else 61) else (if i.val < 88 then 63 else (if i.val < 89 then 52 else 48))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 72 else 61) else (if i.val < 93 then 67 else 37)) else (if i.val < 96 then (if i.val < 95 then 17 else 55) else (if i.val < 97 then 77 else (if i.val < 98 then 27 else 5)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 76 else 93) else (if i.val < 102 then 80 else 7)) else (if i.val < 105 then (if i.val < 104 then 17 else 58) else (if i.val < 106 then 83 else (if i.val < 107 then 80 else 7)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 20 else 72) else (if i.val < 111 then 90 else 91)) else (if i.val < 114 then (if i.val < 113 then 85 else 20) else (if i.val < 115 then 55 else (if i.val < 116 then 94 else 41)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 58 else 80) else (if i.val < 120 then 41 else 58)) else (if i.val < 123 then (if i.val < 122 then 80 else 1) else (if i.val < 124 then 95 else (if i.val < 125 then 61 else 17))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 55 else 44) else (if i.val < 129 then 48 else 20)) else (if i.val < 132 then (if i.val < 131 then 63 else 48) else (if i.val < 133 then 80 else (if i.val < 134 then 7 else 64)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 61 else 27) else (if i.val < 138 then 20 else 20)) else (if i.val < 141 then (if i.val < 140 then 98 else 61) else (if i.val < 142 then 41 else (if i.val < 143 then 48 else 17))))))))

def g32p_supplierGroup15_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 5, 7, 8, 17, 18, 19, 20, 23, 27, 28, 31, 37, 41, 44, 48, 51, 52, 55, 58, 61, 63, 64, 65, 67, 72, 76, 77, 79, 80, 81, 82, 83, 85, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end
