import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0343
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0336
import HodgeLean.Foundations.Program.G32PropFourSixPacked0337
import HodgeLean.Foundations.Program.G32PropFourSixPacked0338
import HodgeLean.Foundations.Program.G32PropFourSixPacked0339
import HodgeLean.Foundations.Program.G32PropFourSixPacked0340
import HodgeLean.Foundations.Program.G32PropFourSixPacked0341
import HodgeLean.Foundations.Program.G32PropFourSixPacked0342
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow05
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_101_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 13 14, g32p_row04_traceSegment_101_0000_0013, g32p_row04_traceSegment_101_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 27 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 27 13 14, g32p_row04_traceSegment_101_0027_0013, g32p_row04_traceSegment_101_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 27 27, g32p_row04_traceSegment_101_0000_0027, g32p_row04_traceSegment_101_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 54 13 14, g32p_row04_traceSegment_101_0054_0013, g32p_row04_traceSegment_101_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 81 13 14, g32p_row04_traceSegment_101_0081_0013, g32p_row04_traceSegment_101_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 54 27 27, g32p_row04_traceSegment_101_0054_0027, g32p_row04_traceSegment_101_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 54 54, g32p_row04_traceSegment_101_0000_0054, g32p_row04_traceSegment_101_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 108 13 14, g32p_row04_traceSegment_101_0108_0013, g32p_row04_traceSegment_101_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 135 13 14, g32p_row04_traceSegment_101_0135_0013, g32p_row04_traceSegment_101_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 108 27 27, g32p_row04_traceSegment_101_0108_0027, g32p_row04_traceSegment_101_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 162 13 14, g32p_row04_traceSegment_101_0162_0013, g32p_row04_traceSegment_101_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 189 13 14, g32p_row04_traceSegment_101_0189_0013, g32p_row04_traceSegment_101_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 162 27 27, g32p_row04_traceSegment_101_0162_0027, g32p_row04_traceSegment_101_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 108 54 54, g32p_row04_traceSegment_101_0108_0054, g32p_row04_traceSegment_101_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 0 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 108 108, g32p_row04_traceSegment_101_0000_0108, g32p_row04_traceSegment_101_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 216 13 14, g32p_row04_traceSegment_101_0216_0013, g32p_row04_traceSegment_101_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 243 13 14, g32p_row04_traceSegment_101_0243_0013, g32p_row04_traceSegment_101_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 216 27 27, g32p_row04_traceSegment_101_0216_0027, g32p_row04_traceSegment_101_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 270 13 14, g32p_row04_traceSegment_101_0270_0013, g32p_row04_traceSegment_101_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 297 13 14, g32p_row04_traceSegment_101_0297_0013, g32p_row04_traceSegment_101_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 270 27 27, g32p_row04_traceSegment_101_0270_0027, g32p_row04_traceSegment_101_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 216 54 54, g32p_row04_traceSegment_101_0216_0054, g32p_row04_traceSegment_101_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 324 13 14, g32p_row04_traceSegment_101_0324_0013, g32p_row04_traceSegment_101_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 351 13 14, g32p_row04_traceSegment_101_0351_0013, g32p_row04_traceSegment_101_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 324 27 27, g32p_row04_traceSegment_101_0324_0027, g32p_row04_traceSegment_101_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 378 13 14, g32p_row04_traceSegment_101_0378_0013, g32p_row04_traceSegment_101_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 405 13 14, g32p_row04_traceSegment_101_0405_0013, g32p_row04_traceSegment_101_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 378 27 27, g32p_row04_traceSegment_101_0378_0027, g32p_row04_traceSegment_101_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 324 54 54, g32p_row04_traceSegment_101_0324_0054, g32p_row04_traceSegment_101_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 216 108 108, g32p_row04_traceSegment_101_0216_0108, g32p_row04_traceSegment_101_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_101 0 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 216 216, g32p_row04_traceSegment_101_0000_0216, g32p_row04_traceSegment_101_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 432 13 14, g32p_row04_traceSegment_101_0432_0013, g32p_row04_traceSegment_101_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 459 13 14, g32p_row04_traceSegment_101_0459_0013, g32p_row04_traceSegment_101_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 432 27 27, g32p_row04_traceSegment_101_0432_0027, g32p_row04_traceSegment_101_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 486 13 14, g32p_row04_traceSegment_101_0486_0013, g32p_row04_traceSegment_101_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 513 13 14, g32p_row04_traceSegment_101_0513_0013, g32p_row04_traceSegment_101_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 486 27 27, g32p_row04_traceSegment_101_0486_0027, g32p_row04_traceSegment_101_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 432 54 54, g32p_row04_traceSegment_101_0432_0054, g32p_row04_traceSegment_101_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 540 13 14, g32p_row04_traceSegment_101_0540_0013, g32p_row04_traceSegment_101_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 567 13 14, g32p_row04_traceSegment_101_0567_0013, g32p_row04_traceSegment_101_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 540 27 27, g32p_row04_traceSegment_101_0540_0027, g32p_row04_traceSegment_101_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 594 13 14, g32p_row04_traceSegment_101_0594_0013, g32p_row04_traceSegment_101_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 621 13 14, g32p_row04_traceSegment_101_0621_0013, g32p_row04_traceSegment_101_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 594 27 27, g32p_row04_traceSegment_101_0594_0027, g32p_row04_traceSegment_101_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 540 54 54, g32p_row04_traceSegment_101_0540_0054, g32p_row04_traceSegment_101_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 432 108 108, g32p_row04_traceSegment_101_0432_0108, g32p_row04_traceSegment_101_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 648 13 14, g32p_row04_traceSegment_101_0648_0013, g32p_row04_traceSegment_101_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 675 13 14, g32p_row04_traceSegment_101_0675_0013, g32p_row04_traceSegment_101_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 648 27 27, g32p_row04_traceSegment_101_0648_0027, g32p_row04_traceSegment_101_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 702 13 14, g32p_row04_traceSegment_101_0702_0013, g32p_row04_traceSegment_101_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 729 13 14, g32p_row04_traceSegment_101_0729_0013, g32p_row04_traceSegment_101_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 702 27 27, g32p_row04_traceSegment_101_0702_0027, g32p_row04_traceSegment_101_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 648 54 54, g32p_row04_traceSegment_101_0648_0054, g32p_row04_traceSegment_101_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 756 13 14, g32p_row04_traceSegment_101_0756_0013, g32p_row04_traceSegment_101_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 783 13 14, g32p_row04_traceSegment_101_0783_0013, g32p_row04_traceSegment_101_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 756 27 27, g32p_row04_traceSegment_101_0756_0027, g32p_row04_traceSegment_101_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 810 13 14, g32p_row04_traceSegment_101_0810_0013, g32p_row04_traceSegment_101_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 837 13 14, g32p_row04_traceSegment_101_0837_0013, g32p_row04_traceSegment_101_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 810 27 27, g32p_row04_traceSegment_101_0810_0027, g32p_row04_traceSegment_101_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 756 54 54, g32p_row04_traceSegment_101_0756_0054, g32p_row04_traceSegment_101_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 648 108 108, g32p_row04_traceSegment_101_0648_0108, g32p_row04_traceSegment_101_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_101 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 432 216 216, g32p_row04_traceSegment_101_0432_0216, g32p_row04_traceSegment_101_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_101 0 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 432 432, g32p_row04_traceSegment_101_0000_0432, g32p_row04_traceSegment_101_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 864 13 14, g32p_row04_traceSegment_101_0864_0013, g32p_row04_traceSegment_101_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 891 13 14, g32p_row04_traceSegment_101_0891_0013, g32p_row04_traceSegment_101_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 864 27 27, g32p_row04_traceSegment_101_0864_0027, g32p_row04_traceSegment_101_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 918 13 14, g32p_row04_traceSegment_101_0918_0013, g32p_row04_traceSegment_101_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 945 13 14, g32p_row04_traceSegment_101_0945_0013, g32p_row04_traceSegment_101_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 918 27 27, g32p_row04_traceSegment_101_0918_0027, g32p_row04_traceSegment_101_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 864 54 54, g32p_row04_traceSegment_101_0864_0054, g32p_row04_traceSegment_101_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 972 13 14, g32p_row04_traceSegment_101_0972_0013, g32p_row04_traceSegment_101_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 999 13 14, g32p_row04_traceSegment_101_0999_0013, g32p_row04_traceSegment_101_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 972 27 27, g32p_row04_traceSegment_101_0972_0027, g32p_row04_traceSegment_101_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1026 13 14, g32p_row04_traceSegment_101_1026_0013, g32p_row04_traceSegment_101_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1053 13 14, g32p_row04_traceSegment_101_1053_0013, g32p_row04_traceSegment_101_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1026 27 27, g32p_row04_traceSegment_101_1026_0027, g32p_row04_traceSegment_101_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 972 54 54, g32p_row04_traceSegment_101_0972_0054, g32p_row04_traceSegment_101_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 864 108 108, g32p_row04_traceSegment_101_0864_0108, g32p_row04_traceSegment_101_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1080 13 14, g32p_row04_traceSegment_101_1080_0013, g32p_row04_traceSegment_101_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1107 13 14, g32p_row04_traceSegment_101_1107_0013, g32p_row04_traceSegment_101_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1080 27 27, g32p_row04_traceSegment_101_1080_0027, g32p_row04_traceSegment_101_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1134 13 14, g32p_row04_traceSegment_101_1134_0013, g32p_row04_traceSegment_101_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1161 13 14, g32p_row04_traceSegment_101_1161_0013, g32p_row04_traceSegment_101_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1134 27 27, g32p_row04_traceSegment_101_1134_0027, g32p_row04_traceSegment_101_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1080 54 54, g32p_row04_traceSegment_101_1080_0054, g32p_row04_traceSegment_101_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1188 13 14, g32p_row04_traceSegment_101_1188_0013, g32p_row04_traceSegment_101_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1215 13 14, g32p_row04_traceSegment_101_1215_0013, g32p_row04_traceSegment_101_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1188 27 27, g32p_row04_traceSegment_101_1188_0027, g32p_row04_traceSegment_101_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1242 13 14, g32p_row04_traceSegment_101_1242_0013, g32p_row04_traceSegment_101_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1269 13 14, g32p_row04_traceSegment_101_1269_0013, g32p_row04_traceSegment_101_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1242 27 27, g32p_row04_traceSegment_101_1242_0027, g32p_row04_traceSegment_101_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1188 54 54, g32p_row04_traceSegment_101_1188_0054, g32p_row04_traceSegment_101_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1080 108 108, g32p_row04_traceSegment_101_1080_0108, g32p_row04_traceSegment_101_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_101 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 864 216 216, g32p_row04_traceSegment_101_0864_0216, g32p_row04_traceSegment_101_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1296 13 14, g32p_row04_traceSegment_101_1296_0013, g32p_row04_traceSegment_101_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1323 13 14, g32p_row04_traceSegment_101_1323_0013, g32p_row04_traceSegment_101_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1296 27 27, g32p_row04_traceSegment_101_1296_0027, g32p_row04_traceSegment_101_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1350 13 14, g32p_row04_traceSegment_101_1350_0013, g32p_row04_traceSegment_101_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1377 13 14, g32p_row04_traceSegment_101_1377_0013, g32p_row04_traceSegment_101_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1350 27 27, g32p_row04_traceSegment_101_1350_0027, g32p_row04_traceSegment_101_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1296 54 54, g32p_row04_traceSegment_101_1296_0054, g32p_row04_traceSegment_101_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1404 13 14, g32p_row04_traceSegment_101_1404_0013, g32p_row04_traceSegment_101_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1431 13 14, g32p_row04_traceSegment_101_1431_0013, g32p_row04_traceSegment_101_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1404 27 27, g32p_row04_traceSegment_101_1404_0027, g32p_row04_traceSegment_101_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1458 13 14, g32p_row04_traceSegment_101_1458_0013, g32p_row04_traceSegment_101_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1485 13 14, g32p_row04_traceSegment_101_1485_0013, g32p_row04_traceSegment_101_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1458 27 27, g32p_row04_traceSegment_101_1458_0027, g32p_row04_traceSegment_101_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1404 54 54, g32p_row04_traceSegment_101_1404_0054, g32p_row04_traceSegment_101_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1296 108 108, g32p_row04_traceSegment_101_1296_0108, g32p_row04_traceSegment_101_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1512 13 14, g32p_row04_traceSegment_101_1512_0013, g32p_row04_traceSegment_101_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1539 13 14, g32p_row04_traceSegment_101_1539_0013, g32p_row04_traceSegment_101_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1512 27 27, g32p_row04_traceSegment_101_1512_0027, g32p_row04_traceSegment_101_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1566 13 14, g32p_row04_traceSegment_101_1566_0013, g32p_row04_traceSegment_101_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1593 13 14, g32p_row04_traceSegment_101_1593_0013, g32p_row04_traceSegment_101_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1566 27 27, g32p_row04_traceSegment_101_1566_0027, g32p_row04_traceSegment_101_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1512 54 54, g32p_row04_traceSegment_101_1512_0054, g32p_row04_traceSegment_101_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1620 13 14, g32p_row04_traceSegment_101_1620_0013, g32p_row04_traceSegment_101_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1647 13 14, g32p_row04_traceSegment_101_1647_0013, g32p_row04_traceSegment_101_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1620 27 27, g32p_row04_traceSegment_101_1620_0027, g32p_row04_traceSegment_101_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1674 13 14, g32p_row04_traceSegment_101_1674_0013, g32p_row04_traceSegment_101_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_101 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_101 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_101_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_101 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1701 13 14, g32p_row04_traceSegment_101_1701_0013, g32p_row04_traceSegment_101_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_101 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1674 27 27, g32p_row04_traceSegment_101_1674_0027, g32p_row04_traceSegment_101_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_101 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1620 54 54, g32p_row04_traceSegment_101_1620_0054, g32p_row04_traceSegment_101_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_101 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1512 108 108, g32p_row04_traceSegment_101_1512_0108, g32p_row04_traceSegment_101_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_101_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_101 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 1296 216 216, g32p_row04_traceSegment_101_1296_0216, g32p_row04_traceSegment_101_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_101 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 864 432 432, g32p_row04_traceSegment_101_0864_0432, g32p_row04_traceSegment_101_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_101_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_101 0 1728 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_101 0 864 864, g32p_row04_traceSegment_101_0000_0864, g32p_row04_traceSegment_101_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 101 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_101_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 96) (g32p_literalTraceValue 3 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_096]
  decide +kernel

theorem g32p_row04_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 97) (g32p_literalTraceValue 3 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_097]
  decide +kernel

theorem g32p_row04_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 98) (g32p_literalTraceValue 3 98)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_098]
  decide +kernel

theorem g32p_row04_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 99) (g32p_literalTraceValue 3 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_099]
  decide +kernel

theorem g32p_row04_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 100) (g32p_literalTraceValue 3 100)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_100]
  decide +kernel

theorem g32p_row04_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 101) (g32p_literalTraceValue 3 101)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row04_traceCoefficients_101]
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

def g32p_row04_generatorIndex : Fin 8 → Fin 408 :=
  ![3, 54, 105, 156, 210, 211, 312, 313]

theorem g32p_row04_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup02_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 3 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 3 g32p_row04_supplierClass
    g32p_row04_supplierClass_isConj g32p_supplierGroup02_support g32p_row04_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row04_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup02_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row04_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 3 c false (g32p_row04_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 3 c true (g32p_row04_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 3 c false (g32p_row04_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 3 c true (g32p_row04_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 3 c false (g32p_row04_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 3 c false (g32p_row04_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 3 c true (g32p_row04_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 3 c true (g32p_row04_coinduced_zero c hc true) 3

theorem g32p_row04_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup02_support →
      g32p_literalTraceValue (g32p_row04_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row04_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup02_support) :
    g32p_literalTraceValue (g32p_row04_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup02_support →
    g32p_literalTraceValue (g32p_row04_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row04_zeroTrace_block_00 r k
  · exact g32p_row04_zeroTrace_block_01 r k
  · exact g32p_row04_zeroTrace_block_02 r k
  · exact g32p_row04_zeroTrace_block_03 r k
  · exact g32p_row04_zeroTrace_block_04 r k
  · exact g32p_row04_zeroTrace_block_05 r k
  · exact g32p_row04_zeroTrace_block_06 r k

theorem g32p_row04_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup02_support) :
    (g32p_recordedInductionGenerators (g32p_row04_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row04_generatorIndex k) c) := by
  rw [g32p_row04_recordedGenerator_zero c hc k, g32p_row04_zeroTrace_arithmetic c k hc]
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

def g32p_row04_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [15552])) else (if i.val < 4 then [1728] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [5184] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [1728] else [10368])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else [1728]))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [1728] else [1728])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else [10368]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [1728])) else (if i.val < 29 then [15552] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [3456] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [10368] else []) else (if i.val < 37 then [] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [1728])) else (if i.val < 42 then [1728] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [15552] else (if i.val < 46 then [5184] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [3456])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [1728] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [1728] else [10368]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [1728] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [1728] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [1728] else (if i.val < 65 then [1728] else [3456])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [1728])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [3456] else [5184]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [15552] else (if i.val < 78 then [1728] else [10368])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [5184])) else (if i.val < 87 then (if i.val < 86 then [1728] else [1728]) else (if i.val < 88 then [15552] else [15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [1728] else (if i.val < 91 then [3456] else [1728])) else (if i.val < 93 then [] else (if i.val < 94 then [15552] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [15552] else [155520])))))))

theorem g32p_row04_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup02_support) :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) c) (g32p_literalTraceValue 3 c)
      [1, 1, 1] (g32p_row04_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row04_tracePolynomial_000
  · exact g32p_row04_tracePolynomial_001
  · exact g32p_row04_tracePolynomial_002
  · exact g32p_row04_tracePolynomial_003
  · exact g32p_row04_tracePolynomial_004
  · exact g32p_row04_tracePolynomial_005
  · exact g32p_row04_tracePolynomial_006
  · exact g32p_row04_tracePolynomial_007
  · exact g32p_row04_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_010
  · exact g32p_row04_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_017
  · exact g32p_row04_tracePolynomial_018
  · exact g32p_row04_tracePolynomial_019
  · exact g32p_row04_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_023
  · exact g32p_row04_tracePolynomial_024
  · exact g32p_row04_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_027
  · exact g32p_row04_tracePolynomial_028
  · exact g32p_row04_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_031
  · exact g32p_row04_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_034
  · exact g32p_row04_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_040
  · exact g32p_row04_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_043
  · exact g32p_row04_tracePolynomial_044
  · exact g32p_row04_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_050
  · exact g32p_row04_tracePolynomial_051
  · exact g32p_row04_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_055
  · exact g32p_row04_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_058
  · exact g32p_row04_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_063
  · exact g32p_row04_tracePolynomial_064
  · exact g32p_row04_tracePolynomial_065
  · exact g32p_row04_tracePolynomial_066
  · exact g32p_row04_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_071
  · exact g32p_row04_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup02_support) hc)
  · exact g32p_row04_tracePolynomial_074
  · exact g32p_row04_tracePolynomial_075
  · exact g32p_row04_tracePolynomial_076
  · exact g32p_row04_tracePolynomial_077
  · exact g32p_row04_tracePolynomial_078
  · exact g32p_row04_tracePolynomial_079
  · exact g32p_row04_tracePolynomial_080
  · exact g32p_row04_tracePolynomial_081
  · exact g32p_row04_tracePolynomial_082
  · exact g32p_row04_tracePolynomial_083
  · exact g32p_row04_tracePolynomial_084
  · exact g32p_row04_tracePolynomial_085
  · exact g32p_row04_tracePolynomial_086
  · exact g32p_row04_tracePolynomial_087
  · exact g32p_row04_tracePolynomial_088
  · exact g32p_row04_tracePolynomial_089
  · exact g32p_row04_tracePolynomial_090
  · exact g32p_row04_tracePolynomial_091
  · exact g32p_row04_tracePolynomial_092
  · exact g32p_row04_tracePolynomial_093
  · exact g32p_row04_tracePolynomial_094
  · exact g32p_row04_tracePolynomial_095
  · exact g32p_row04_tracePolynomial_096
  · exact g32p_row04_tracePolynomial_097
  · exact g32p_row04_tracePolynomial_098
  · exact g32p_row04_tracePolynomial_099
  · exact g32p_row04_tracePolynomial_100
  · exact g32p_row04_tracePolynomial_101

theorem g32p_row04_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 3 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 3 c) := by
  by_cases hc : c ∈ g32p_supplierGroup02_support
  · have hclass (j : Fin 1728) :
        IsConj (g32p_literalRepresentative c) (g32p_row04_groupEquiv j : g32p_G) ↔
          g32p_row04_supplierClassifier j = c := by
      simpa only [g32p_row04_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row04_supplierClass_iff (g32p_row04_groupEquiv j) c
    have hχ (j : Fin 1728) :
        (g32p_recordedSupplierCharacters 3 (g32p_row04_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row04_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 3 (show (g32p_recordedSuppliers 3).H from g32p_row04_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row04_characterValues (g32p_row04_groupEquiv.symm (g32p_row04_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 3).H (g32p_recordedSupplierCharacters 3)
      (g32p_literalRepresentative c) g32p_row04_groupEquiv g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) c 3 1728
      (g32p_literalCentralizer c) (g32p_literalTraceValue 3 c) [1, 1, 1]
      (g32p_row04_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row04_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 3)))
      (g32p_row04_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row04_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row04_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
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

theorem g32p_row04_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_0 r
  · exact g32p_row04_variantArithmetic_01_0 r
  · exact g32p_row04_variantArithmetic_02_0 r
  · exact g32p_row04_variantArithmetic_03_0 r
  · exact g32p_row04_variantArithmetic_04_0 r
  · exact g32p_row04_variantArithmetic_05_0 r
  · exact g32p_row04_variantArithmetic_06_0 r

theorem g32p_row04_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_1 r
  · exact g32p_row04_variantArithmetic_01_1 r
  · exact g32p_row04_variantArithmetic_02_1 r
  · exact g32p_row04_variantArithmetic_03_1 r
  · exact g32p_row04_variantArithmetic_04_1 r
  · exact g32p_row04_variantArithmetic_05_1 r
  · exact g32p_row04_variantArithmetic_06_1 r

theorem g32p_row04_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_2 r
  · exact g32p_row04_variantArithmetic_01_2 r
  · exact g32p_row04_variantArithmetic_02_2 r
  · exact g32p_row04_variantArithmetic_03_2 r
  · exact g32p_row04_variantArithmetic_04_2 r
  · exact g32p_row04_variantArithmetic_05_2 r
  · exact g32p_row04_variantArithmetic_06_2 r

theorem g32p_row04_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_3 r
  · exact g32p_row04_variantArithmetic_01_3 r
  · exact g32p_row04_variantArithmetic_02_3 r
  · exact g32p_row04_variantArithmetic_03_3 r
  · exact g32p_row04_variantArithmetic_04_3 r
  · exact g32p_row04_variantArithmetic_05_3 r
  · exact g32p_row04_variantArithmetic_06_3 r

theorem g32p_row04_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_4 r
  · exact g32p_row04_variantArithmetic_01_4 r
  · exact g32p_row04_variantArithmetic_02_4 r
  · exact g32p_row04_variantArithmetic_03_4 r
  · exact g32p_row04_variantArithmetic_04_4 r
  · exact g32p_row04_variantArithmetic_05_4 r
  · exact g32p_row04_variantArithmetic_06_4 r

theorem g32p_row04_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_5 r
  · exact g32p_row04_variantArithmetic_01_5 r
  · exact g32p_row04_variantArithmetic_02_5 r
  · exact g32p_row04_variantArithmetic_03_5 r
  · exact g32p_row04_variantArithmetic_04_5 r
  · exact g32p_row04_variantArithmetic_05_5 r
  · exact g32p_row04_variantArithmetic_06_5 r

theorem g32p_row04_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_6 r
  · exact g32p_row04_variantArithmetic_01_6 r
  · exact g32p_row04_variantArithmetic_02_6 r
  · exact g32p_row04_variantArithmetic_03_6 r
  · exact g32p_row04_variantArithmetic_04_6 r
  · exact g32p_row04_variantArithmetic_05_6 r
  · exact g32p_row04_variantArithmetic_06_6 r

theorem g32p_row04_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row04_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 3 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row04_variantArithmetic_00_7 r
  · exact g32p_row04_variantArithmetic_01_7 r
  · exact g32p_row04_variantArithmetic_02_7 r
  · exact g32p_row04_variantArithmetic_03_7 r
  · exact g32p_row04_variantArithmetic_04_7 r
  · exact g32p_row04_variantArithmetic_05_7 r
  · exact g32p_row04_variantArithmetic_06_7 r

theorem g32p_row04_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row04_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row04_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 3 c _ (g32p_row04_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row04_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup03_source : Fin 486 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 243 then (if i.val < 121 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (6, 14) else (38, 210))) else (if i.val < 5 then (if i.val < 4 then (1, 207) else (81, 44)) else (if i.val < 6 then (52, 113) else (26, 80)))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then (2, 188) else (70, 57)) else (if i.val < 10 then (141, 134) else (27, 46))) else (if i.val < 13 then (if i.val < 12 then (102, 72) else (105, 28)) else (if i.val < 14 then (78, 118) else (1, 190))))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then (85, 7) else (if i.val < 17 then (76, 108) else (108, 99))) else (if i.val < 20 then (if i.val < 19 then (20, 160) else (56, 124)) else (if i.val < 21 then (93, 207) else (48, 157)))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then (67, 15) else (21, 209)) else (if i.val < 25 then (5, 204) else (128, 128))) else (if i.val < 28 then (if i.val < 27 then (58, 254) else (15, 142)) else (if i.val < 29 then (128, 237) else (109, 3)))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then (25, 158) else (if i.val < 32 then (80, 167) else (110, 204))) else (if i.val < 35 then (if i.val < 34 then (11, 228) else (69, 10)) else (if i.val < 36 then (55, 10) else (83, 170)))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then (131, 208) else (1, 98)) else (if i.val < 40 then (125, 228) else (96, 182))) else (if i.val < 43 then (if i.val < 42 then (0, 82) else (84, 15)) else (if i.val < 44 then (14, 242) else (115, 173))))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then (133, 249) else (if i.val < 47 then (25, 9) else (20, 14))) else (if i.val < 50 then (if i.val < 49 then (112, 62) else (1, 161)) else (if i.val < 51 then (84, 17) else (120, 235)))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then (106, 208) else (110, 91)) else (if i.val < 55 then (31, 130) else (75, 170))) else (if i.val < 58 then (if i.val < 57 then (101, 92) else (61, 180)) else (if i.val < 59 then (5, 18) else (57, 172))))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then (104, 203) else (if i.val < 62 then (32, 229) else (43, 230))) else (if i.val < 65 then (if i.val < 64 then (27, 128) else (38, 220)) else (if i.val < 66 then (95, 82) else (41, 212)))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then (95, 142) else (1, 31)) else (if i.val < 70 then (57, 196) else (118, 141))) else (if i.val < 73 then (if i.val < 72 then (83, 231) else (120, 238)) else (if i.val < 74 then (77, 240) else (5, 232))))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then (103, 193) else (if i.val < 77 then (67, 201) else (10, 213))) else (if i.val < 80 then (if i.val < 79 then (100, 163) else (86, 150)) else (if i.val < 81 then (44, 127) else (20, 109)))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then (81, 24) else (75, 46)) else (if i.val < 85 then (130, 209) else (55, 78))) else (if i.val < 88 then (if i.val < 87 then (48, 185) else (108, 108)) else (if i.val < 89 then (84, 250) else (82, 36)))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then (52, 143) else (if i.val < 92 then (64, 7) else (5, 121))) else (if i.val < 95 then (if i.val < 94 then (68, 238) else (114, 62)) else (if i.val < 96 then (118, 104) else (138, 63)))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then (76, 158) else (41, 30)) else (if i.val < 100 then (82, 71) else (59, 27))) else (if i.val < 103 then (if i.val < 102 then (123, 63) else (132, 211)) else (if i.val < 104 then (93, 96) else (55, 211))))) else (if i.val < 113 then (if i.val < 109 then (if i.val < 107 then (if i.val < 106 then (112, 8) else (77, 9)) else (if i.val < 108 then (111, 172) else (92, 37))) else (if i.val < 111 then (if i.val < 110 then (132, 184) else (29, 39)) else (if i.val < 112 then (132, 180) else (113, 220)))) else (if i.val < 117 then (if i.val < 115 then (if i.val < 114 then (85, 18) else (113, 221)) else (if i.val < 116 then (52, 22) else (118, 108))) else (if i.val < 119 then (if i.val < 118 then (98, 48) else (106, 111)) else (if i.val < 120 then (85, 15) else (107, 42)))))))) else (if i.val < 182 then (if i.val < 151 then (if i.val < 136 then (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then (69, 22) else (if i.val < 123 then (128, 217) else (14, 235))) else (if i.val < 126 then (if i.val < 125 then (58, 253) else (81, 168)) else (if i.val < 127 then (47, 119) else (48, 130)))) else (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then (28, 42) else (0, 89)) else (if i.val < 131 then (49, 64) else (40, 87))) else (if i.val < 134 then (if i.val < 133 then (118, 62) else (17, 157)) else (if i.val < 135 then (52, 33) else (56, 39))))) else (if i.val < 143 then (if i.val < 139 then (if i.val < 137 then (30, 140) else (if i.val < 138 then (65, 229) else (129, 204))) else (if i.val < 141 then (if i.val < 140 then (83, 161) else (121, 117)) else (if i.val < 142 then (95, 241) else (99, 137)))) else (if i.val < 147 then (if i.val < 145 then (if i.val < 144 then (45, 70) else (131, 195)) else (if i.val < 146 then (110, 197) else (115, 156))) else (if i.val < 149 then (if i.val < 148 then (107, 237) else (0, 96)) else (if i.val < 150 then (121, 191) else (91, 150)))))) else (if i.val < 166 then (if i.val < 158 then (if i.val < 154 then (if i.val < 152 then (127, 82) else (if i.val < 153 then (116, 178) else (120, 204))) else (if i.val < 156 then (if i.val < 155 then (38, 47) else (112, 65)) else (if i.val < 157 then (56, 132) else (11, 7)))) else (if i.val < 162 then (if i.val < 160 then (if i.val < 159 then (71, 161) else (133, 192)) else (if i.val < 161 then (98, 55) else (90, 224))) else (if i.val < 164 then (if i.val < 163 then (127, 83) else (119, 25)) else (if i.val < 165 then (105, 212) else (33, 136))))) else (if i.val < 174 then (if i.val < 170 then (if i.val < 168 then (if i.val < 167 then (45, 98) else (106, 45)) else (if i.val < 169 then (108, 109) else (128, 181))) else (if i.val < 172 then (if i.val < 171 then (31, 190) else (99, 131)) else (if i.val < 173 then (25, 34) else (90, 194)))) else (if i.val < 178 then (if i.val < 176 then (if i.val < 175 then (103, 26) else (72, 129)) else (if i.val < 177 then (91, 17) else (107, 212))) else (if i.val < 180 then (if i.val < 179 then (111, 236) else (128, 197)) else (if i.val < 181 then (110, 20) else (110, 72))))))) else (if i.val < 212 then (if i.val < 197 then (if i.val < 189 then (if i.val < 185 then (if i.val < 183 then (71, 146) else (if i.val < 184 then (57, 20) else (14, 212))) else (if i.val < 187 then (if i.val < 186 then (109, 91) else (71, 81)) else (if i.val < 188 then (35, 53) else (69, 214)))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then (14, 230) else (98, 210)) else (if i.val < 192 then (116, 31) else (97, 182))) else (if i.val < 195 then (if i.val < 194 then (96, 123) else (96, 172)) else (if i.val < 196 then (14, 213) else (110, 199))))) else (if i.val < 204 then (if i.val < 200 then (if i.val < 198 then (53, 6) else (if i.val < 199 then (87, 127) else (4, 131))) else (if i.val < 202 then (if i.val < 201 then (58, 148) else (57, 34)) else (if i.val < 203 then (120, 164) else (54, 254)))) else (if i.val < 208 then (if i.val < 206 then (if i.val < 205 then (90, 47) else (75, 72)) else (if i.val < 207 then (128, 15) else (75, 184))) else (if i.val < 210 then (if i.val < 209 then (86, 153) else (125, 153)) else (if i.val < 211 then (95, 63) else (130, 252)))))) else (if i.val < 227 then (if i.val < 219 then (if i.val < 215 then (if i.val < 213 then (105, 87) else (if i.val < 214 then (84, 255) else (86, 109))) else (if i.val < 217 then (if i.val < 216 then (86, 209) else (10, 249)) else (if i.val < 218 then (102, 177) else (68, 170)))) else (if i.val < 223 then (if i.val < 221 then (if i.val < 220 then (86, 107) else (141, 131)) else (if i.val < 222 then (131, 15) else (60, 249))) else (if i.val < 225 then (if i.val < 224 then (94, 161) else (126, 224)) else (if i.val < 226 then (57, 200) else (39, 78))))) else (if i.val < 235 then (if i.val < 231 then (if i.val < 229 then (if i.val < 228 then (130, 137) else (94, 167)) else (if i.val < 230 then (123, 150) else (28, 11))) else (if i.val < 233 then (if i.val < 232 then (68, 15) else (84, 38)) else (if i.val < 234 then (111, 65) else (131, 80)))) else (if i.val < 239 then (if i.val < 237 then (if i.val < 236 then (107, 45) else (26, 216)) else (if i.val < 238 then (57, 173) else (57, 235))) else (if i.val < 241 then (if i.val < 240 then (126, 105) else (56, 143)) else (if i.val < 242 then (0, 85) else (137, 137))))))))) else (if i.val < 364 then (if i.val < 303 then (if i.val < 273 then (if i.val < 258 then (if i.val < 250 then (if i.val < 246 then (if i.val < 244 then (130, 158) else (if i.val < 245 then (5, 169) else (125, 161))) else (if i.val < 248 then (if i.val < 247 then (125, 134) else (41, 221)) else (if i.val < 249 then (30, 240) else (131, 69)))) else (if i.val < 254 then (if i.val < 252 then (if i.val < 251 then (106, 134) else (61, 35)) else (if i.val < 253 then (61, 98) else (16, 59))) else (if i.val < 256 then (if i.val < 255 then (35, 248) else (92, 84)) else (if i.val < 257 then (104, 187) else (71, 210))))) else (if i.val < 265 then (if i.val < 261 then (if i.val < 259 then (55, 25) else (if i.val < 260 then (101, 222) else (126, 247))) else (if i.val < 263 then (if i.val < 262 then (131, 84) else (3, 138)) else (if i.val < 264 then (28, 10) else (104, 227)))) else (if i.val < 269 then (if i.val < 267 then (if i.val < 266 then (66, 201) else (141, 145)) else (if i.val < 268 then (12, 222) else (52, 210))) else (if i.val < 271 then (if i.val < 270 then (33, 36) else (50, 200)) else (if i.val < 272 then (33, 80) else (30, 254)))))) else (if i.val < 288 then (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (78, 161) else (if i.val < 275 then (67, 188) else (77, 229))) else (if i.val < 278 then (if i.val < 277 then (49, 132) else (115, 3)) else (if i.val < 279 then (86, 106) else (29, 103)))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then (66, 218) else (128, 41)) else (if i.val < 283 then (16, 25) else (23, 133))) else (if i.val < 286 then (if i.val < 285 then (38, 216) else (11, 27)) else (if i.val < 287 then (129, 10) else (113, 242))))) else (if i.val < 295 then (if i.val < 291 then (if i.val < 289 then (113, 254) else (if i.val < 290 then (88, 124) else (135, 95))) else (if i.val < 293 then (if i.val < 292 then (88, 56) else (34, 180)) else (if i.val < 294 then (56, 59) else (9, 135)))) else (if i.val < 299 then (if i.val < 297 then (if i.val < 296 then (129, 159) else (132, 153)) else (if i.val < 298 then (140, 178) else (17, 163))) else (if i.val < 301 then (if i.val < 300 then (88, 148) else (114, 194)) else (if i.val < 302 then (18, 51) else (35, 236))))))) else (if i.val < 333 then (if i.val < 318 then (if i.val < 310 then (if i.val < 306 then (if i.val < 304 then (68, 93) else (if i.val < 305 then (88, 99) else (13, 158))) else (if i.val < 308 then (if i.val < 307 then (56, 78) else (80, 43)) else (if i.val < 309 then (22, 25) else (60, 45)))) else (if i.val < 314 then (if i.val < 312 then (if i.val < 311 then (121, 22) else (140, 107)) else (if i.val < 313 then (88, 123) else (28, 29))) else (if i.val < 316 then (if i.val < 315 then (79, 158) else (85, 35)) else (if i.val < 317 then (31, 129) else (140, 104))))) else (if i.val < 325 then (if i.val < 321 then (if i.val < 319 then (34, 113) else (if i.val < 320 then (0, 101) else (105, 19))) else (if i.val < 323 then (if i.val < 322 then (93, 28) else (107, 194)) else (if i.val < 324 then (43, 83) else (32, 4)))) else (if i.val < 329 then (if i.val < 327 then (if i.val < 326 then (118, 0) else (131, 3)) else (if i.val < 328 then (92, 213) else (111, 157))) else (if i.val < 331 then (if i.val < 330 then (126, 82) else (111, 174)) else (if i.val < 332 then (127, 118) else (86, 45)))))) else (if i.val < 348 then (if i.val < 340 then (if i.val < 336 then (if i.val < 334 then (0, 79) else (if i.val < 335 then (92, 155) else (34, 170))) else (if i.val < 338 then (if i.val < 337 then (138, 241) else (82, 85)) else (if i.val < 339 then (85, 139) else (45, 12)))) else (if i.val < 344 then (if i.val < 342 then (if i.val < 341 then (52, 3) else (96, 75)) else (if i.val < 343 then (15, 39) else (134, 167))) else (if i.val < 346 then (if i.val < 345 then (29, 230) else (98, 20)) else (if i.val < 347 then (123, 103) else (87, 199))))) else (if i.val < 356 then (if i.val < 352 then (if i.val < 350 then (if i.val < 349 then (81, 166) else (100, 251)) else (if i.val < 351 then (142, 69) else (56, 224))) else (if i.val < 354 then (if i.val < 353 then (94, 2) else (38, 235)) else (if i.val < 355 then (92, 6) else (56, 212)))) else (if i.val < 360 then (if i.val < 358 then (if i.val < 357 then (113, 247) else (113, 240)) else (if i.val < 359 then (87, 185) else (78, 165))) else (if i.val < 362 then (if i.val < 361 then (131, 172) else (52, 37)) else (if i.val < 363 then (107, 164) else (17, 236)))))))) else (if i.val < 425 then (if i.val < 394 then (if i.val < 379 then (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then (131, 220) else (if i.val < 366 then (84, 42) else (131, 205))) else (if i.val < 369 then (if i.val < 368 then (62, 102) else (5, 188)) else (if i.val < 370 then (112, 84) else (53, 45)))) else (if i.val < 375 then (if i.val < 373 then (if i.val < 372 then (25, 126) else (116, 30)) else (if i.val < 374 then (82, 210) else (85, 96))) else (if i.val < 377 then (if i.val < 376 then (43, 105) else (47, 156)) else (if i.val < 378 then (57, 22) else (80, 5))))) else (if i.val < 386 then (if i.val < 382 then (if i.val < 380 then (29, 36) else (if i.val < 381 then (81, 142) else (82, 158))) else (if i.val < 384 then (if i.val < 383 then (128, 235) else (4, 141)) else (if i.val < 385 then (50, 170) else (56, 139)))) else (if i.val < 390 then (if i.val < 388 then (if i.val < 387 then (81, 206) else (31, 201)) else (if i.val < 389 then (46, 21) else (58, 200))) else (if i.val < 392 then (if i.val < 391 then (116, 66) else (125, 66)) else (if i.val < 393 then (108, 119) else (14, 208)))))) else (if i.val < 409 then (if i.val < 401 then (if i.val < 397 then (if i.val < 395 then (108, 17) else (if i.val < 396 then (54, 151) else (98, 240))) else (if i.val < 399 then (if i.val < 398 then (124, 180) else (112, 97)) else (if i.val < 400 then (111, 242) else (131, 210)))) else (if i.val < 405 then (if i.val < 403 then (if i.val < 402 then (51, 98) else (31, 188)) else (if i.val < 404 then (55, 104) else (37, 177))) else (if i.val < 407 then (if i.val < 406 then (45, 123) else (71, 53)) else (if i.val < 408 then (61, 232) else (63, 0))))) else (if i.val < 417 then (if i.val < 413 then (if i.val < 411 then (if i.val < 410 then (90, 39) else (111, 84)) else (if i.val < 412 then (32, 69) else (115, 248))) else (if i.val < 415 then (if i.val < 414 then (128, 192) else (112, 57)) else (if i.val < 416 then (57, 37) else (62, 34)))) else (if i.val < 421 then (if i.val < 419 then (if i.val < 418 then (109, 191) else (6, 90)) else (if i.val < 420 then (136, 130) else (29, 120))) else (if i.val < 423 then (if i.val < 422 then (60, 24) else (32, 120)) else (if i.val < 424 then (81, 20) else (37, 69))))))) else (if i.val < 455 then (if i.val < 440 then (if i.val < 432 then (if i.val < 428 then (if i.val < 426 then (83, 106) else (if i.val < 427 then (5, 83) else (49, 59))) else (if i.val < 430 then (if i.val < 429 then (57, 216) else (86, 217)) else (if i.val < 431 then (83, 197) else (56, 152)))) else (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then (101, 252) else (141, 103)) else (if i.val < 435 then (57, 154) else (31, 205))) else (if i.val < 438 then (if i.val < 437 then (110, 145) else (104, 99)) else (if i.val < 439 then (75, 174) else (15, 0))))) else (if i.val < 447 then (if i.val < 443 then (if i.val < 441 then (131, 47) else (if i.val < 442 then (26, 93) else (5, 194))) else (if i.val < 445 then (if i.val < 444 then (97, 179) else (89, 224)) else (if i.val < 446 then (103, 175) else (86, 136)))) else (if i.val < 451 then (if i.val < 449 then (if i.val < 448 then (110, 179) else (31, 225)) else (if i.val < 450 then (47, 227) else (77, 27))) else (if i.val < 453 then (if i.val < 452 then (127, 20) else (41, 94)) else (if i.val < 454 then (56, 178) else (41, 136)))))) else (if i.val < 470 then (if i.val < 462 then (if i.val < 458 then (if i.val < 456 then (141, 108) else (if i.val < 457 then (32, 231) else (45, 228))) else (if i.val < 460 then (if i.val < 459 then (86, 102) else (131, 8)) else (if i.val < 461 then (12, 131) else (42, 35)))) else (if i.val < 466 then (if i.val < 464 then (if i.val < 463 then (55, 108) else (130, 151)) else (if i.val < 465 then (49, 94) else (32, 139))) else (if i.val < 468 then (if i.val < 467 then (113, 241) else (51, 24)) else (if i.val < 469 then (28, 196) else (56, 84))))) else (if i.val < 478 then (if i.val < 474 then (if i.val < 472 then (if i.val < 471 then (85, 37) else (80, 186)) else (if i.val < 473 then (31, 132) else (109, 37))) else (if i.val < 476 then (if i.val < 475 then (39, 229) else (58, 250)) else (if i.val < 477 then (121, 52) else (80, 139)))) else (if i.val < 482 then (if i.val < 480 then (if i.val < 479 then (27, 64) else (80, 128)) else (if i.val < 481 then (14, 184) else (92, 167))) else (if i.val < 484 then (if i.val < 483 then (94, 251) else (11, 209)) else (if i.val < 485 then (30, 204) else (33, 193))))))))))

def g32p_supplierGroup03_classify : Fin 486 → Fin 102 :=
  fun i => (if i.val < 243 then (if i.val < 121 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 8 else 35)) else (if i.val < 5 then (if i.val < 4 then 2 else 74) else (if i.val < 6 then 74 else 45))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 18 else 54) else (if i.val < 10 then 54 else 59)) else (if i.val < 13 then (if i.val < 12 then 54 else 59) else (if i.val < 14 then 59 else 1)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 65 else (if i.val < 17 then 65 else 68)) else (if i.val < 20 then (if i.val < 19 then 65 else 78) else (if i.val < 21 then 68 else 65))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 68 else 78) else (if i.val < 25 then 8 else 68)) else (if i.val < 28 then (if i.val < 27 then 8 else 3) else (if i.val < 29 then 42 else 42))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 82 else (if i.val < 32 then 42 else 81)) else (if i.val < 35 then (if i.val < 34 then 82 else 42) else (if i.val < 36 then 81 else 81))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 14 else 82) else (if i.val < 40 then 14 else 42)) else (if i.val < 43 then (if i.val < 42 then 82 else 81) else (if i.val < 44 then 2 else 14)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 14 else (if i.val < 47 then 82 else 2)) else (if i.val < 50 then (if i.val < 49 then 14 else 74) else (if i.val < 51 then 50 else 50))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 36 else 50) else (if i.val < 55 then 87 else 36)) else (if i.val < 58 then (if i.val < 57 then 50 else 36) else (if i.val < 59 then 87 else 23)))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then 36 else (if i.val < 62 then 23 else 50)) else (if i.val < 65 then (if i.val < 64 then 87 else 36) else (if i.val < 66 then 23 else 18))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 23 else 36) else (if i.val < 70 then 23 else 23)) else (if i.val < 73 then (if i.val < 72 then 11 else 50) else (if i.val < 74 then 36 else 18)))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then 36 else (if i.val < 77 then 23 else 18)) else (if i.val < 80 then (if i.val < 79 then 54 else 23) else (if i.val < 81 then 11 else 36))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then 18 else 54) else (if i.val < 85 then 54 else 11)) else (if i.val < 88 then (if i.val < 87 then 35 else 43) else (if i.val < 89 then 35 else 40))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then 43 else (if i.val < 92 then 35 else 79)) else (if i.val < 95 then (if i.val < 94 then 40 else 9) else (if i.val < 96 then 43 else 9))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then 35 else 79) else (if i.val < 100 then 79 else 11)) else (if i.val < 103 then (if i.val < 102 then 9 else 9) else (if i.val < 104 then 43 else 11)))) else (if i.val < 113 then (if i.val < 109 then (if i.val < 107 then (if i.val < 106 then 9 else 91) else (if i.val < 108 then 35 else 40)) else (if i.val < 111 then (if i.val < 110 then 9 else 79) else (if i.val < 112 then 9 else 9))) else (if i.val < 117 then (if i.val < 115 then (if i.val < 114 then 89 else 9) else (if i.val < 116 then 89 else 43)) else (if i.val < 119 then (if i.val < 118 then 9 else 91) else (if i.val < 120 then 89 else 91))))))) else (if i.val < 182 then (if i.val < 151 then (if i.val < 136 then (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then 43 else (if i.val < 123 then 40 else 1)) else (if i.val < 126 then (if i.val < 125 then 9 else 79) else (if i.val < 127 then 11 else 65))) else (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 89 else 89) else (if i.val < 131 then 91 else 68)) else (if i.val < 134 then (if i.val < 133 then 43 else 1) else (if i.val < 135 then 65 else 89)))) else (if i.val < 143 then (if i.val < 139 then (if i.val < 137 then 78 else (if i.val < 138 then 68 else 74)) else (if i.val < 141 then (if i.val < 140 then 45 else 45) else (if i.val < 142 then 74 else 45))) else (if i.val < 147 then (if i.val < 145 then (if i.val < 144 then 45 else 15) else (if i.val < 146 then 45 else 15)) else (if i.val < 149 then (if i.val < 148 then 74 else 96) else (if i.val < 150 then 45 else 29))))) else (if i.val < 166 then (if i.val < 158 then (if i.val < 154 then (if i.val < 152 then 29 else (if i.val < 153 then 15 else 45)) else (if i.val < 156 then (if i.val < 155 then 29 else 15) else (if i.val < 157 then 76 else 74))) else (if i.val < 162 then (if i.val < 160 then (if i.val < 159 then 45 else 29) else (if i.val < 161 then 45 else 15)) else (if i.val < 164 then (if i.val < 163 then 29 else 42) else (if i.val < 165 then 15 else 6)))) else (if i.val < 174 then (if i.val < 170 then (if i.val < 168 then (if i.val < 167 then 45 else 29) else (if i.val < 169 then 42 else 42)) else (if i.val < 172 then (if i.val < 171 then 76 else 45) else (if i.val < 173 then 45 else 15))) else (if i.val < 178 then (if i.val < 176 then (if i.val < 175 then 29 else 45) else (if i.val < 177 then 15 else 6)) else (if i.val < 180 then (if i.val < 179 then 78 else 42) else (if i.val < 181 then 42 else 51)))))) else (if i.val < 212 then (if i.val < 197 then (if i.val < 189 then (if i.val < 185 then (if i.val < 183 then 45 else (if i.val < 184 then 15 else 76)) else (if i.val < 187 then (if i.val < 186 then 42 else 51) else (if i.val < 188 then 51 else 45))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then 3 else 45) else (if i.val < 192 then 29 else 45)) else (if i.val < 195 then (if i.val < 194 then 42 else 6) else (if i.val < 196 then 78 else 81)))) else (if i.val < 204 then (if i.val < 200 then (if i.val < 198 then 42 else (if i.val < 199 then 51 else 82)) else (if i.val < 202 then (if i.val < 201 then 51 else 3) else (if i.val < 203 then 42 else 81))) else (if i.val < 208 then (if i.val < 206 then (if i.val < 205 then 14 else 54) else (if i.val < 207 then 66 else 59)) else (if i.val < 210 then (if i.val < 209 then 6 else 59) else (if i.val < 211 then 6 else 54))))) else (if i.val < 227 then (if i.val < 219 then (if i.val < 215 then (if i.val < 213 then 64 else (if i.val < 214 then 66 else 6)) else (if i.val < 217 then (if i.val < 216 then 6 else 6) else (if i.val < 218 then 59 else 6))) else (if i.val < 223 then (if i.val < 221 then (if i.val < 220 then 6 else 86) else (if i.val < 222 then 54 else 64)) else (if i.val < 225 then (if i.val < 224 then 6 else 66) else (if i.val < 226 then 6 else 6)))) else (if i.val < 235 then (if i.val < 231 then (if i.val < 229 then (if i.val < 228 then 86 else 6) else (if i.val < 230 then 50 else 59)) else (if i.val < 233 then (if i.val < 232 then 6 else 85) else (if i.val < 234 then 86 else 86))) else (if i.val < 239 then (if i.val < 237 then (if i.val < 236 then 66 else 64) else (if i.val < 238 then 6 else 6)) else (if i.val < 241 then (if i.val < 240 then 66 else 76) else (if i.val < 242 then 85 else 50)))))))) else (if i.val < 364 then (if i.val < 303 then (if i.val < 273 then (if i.val < 258 then (if i.val < 250 then (if i.val < 246 then (if i.val < 244 then 86 else (if i.val < 245 then 85 else 36)) else (if i.val < 248 then (if i.val < 247 then 59 else 6) else (if i.val < 249 then 85 else 86))) else (if i.val < 254 then (if i.val < 252 then (if i.val < 251 then 35 else 36) else (if i.val < 253 then 66 else 6)) else (if i.val < 256 then (if i.val < 255 then 64 else 6) else (if i.val < 257 then 66 else 85)))) else (if i.val < 265 then (if i.val < 261 then (if i.val < 259 then 85 else (if i.val < 260 then 50 else 36)) else (if i.val < 263 then (if i.val < 262 then 86 else 36) else (if i.val < 264 then 35 else 36))) else (if i.val < 269 then (if i.val < 267 then (if i.val < 266 then 6 else 86) else (if i.val < 268 then 36 else 18)) else (if i.val < 271 then (if i.val < 270 then 6 else 64) else (if i.val < 272 then 6 else 85))))) else (if i.val < 288 then (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then 66 else (if i.val < 275 then 6 else 36)) else (if i.val < 278 then (if i.val < 277 then 36 else 35) else (if i.val < 279 then 23 else 18))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then 6 else 36) else (if i.val < 283 then 18 else 18)) else (if i.val < 286 then (if i.val < 285 then 65 else 67) else (if i.val < 287 then 68 else 10)))) else (if i.val < 295 then (if i.val < 291 then (if i.val < 289 then 25 else (if i.val < 290 then 8 else 68)) else (if i.val < 293 then (if i.val < 292 then 10 else 8) else (if i.val < 294 then 35 else 65))) else (if i.val < 299 then (if i.val < 297 then (if i.val < 296 then 68 else 25) else (if i.val < 298 then 68 else 8)) else (if i.val < 301 then (if i.val < 300 then 25 else 35) else (if i.val < 302 then 8 else 2)))))) else (if i.val < 333 then (if i.val < 318 then (if i.val < 310 then (if i.val < 306 then (if i.val < 304 then 68 else (if i.val < 305 then 25 else 35)) else (if i.val < 308 then (if i.val < 307 then 35 else 35) else (if i.val < 309 then 67 else 25))) else (if i.val < 314 then (if i.val < 312 then (if i.val < 311 then 25 else 68) else (if i.val < 313 then 25 else 35)) else (if i.val < 316 then (if i.val < 315 then 35 else 35) else (if i.val < 317 then 35 else 68)))) else (if i.val < 325 then (if i.val < 321 then (if i.val < 319 then 25 else (if i.val < 320 then 101 else 35)) else (if i.val < 323 then (if i.val < 322 then 43 else 40) else (if i.val < 324 then 67 else 10))) else (if i.val < 329 then (if i.val < 327 then (if i.val < 326 then 68 else 25) else (if i.val < 328 then 68 else 35)) else (if i.val < 331 then (if i.val < 330 then 35 else 35) else (if i.val < 332 then 35 else 40))))) else (if i.val < 348 then (if i.val < 340 then (if i.val < 336 then (if i.val < 334 then 79 else (if i.val < 335 then 40 else 10)) else (if i.val < 338 then (if i.val < 337 then 35 else 79) else (if i.val < 339 then 10 else 8))) else (if i.val < 344 then (if i.val < 342 then (if i.val < 341 then 35 else 68) else (if i.val < 343 then 8 else 40)) else (if i.val < 346 then (if i.val < 345 then 79 else 45) else (if i.val < 347 then 45 else 10)))) else (if i.val < 356 then (if i.val < 352 then (if i.val < 350 then (if i.val < 349 then 79 else 45) else (if i.val < 351 then 9 else 10)) else (if i.val < 354 then (if i.val < 353 then 68 else 35) else (if i.val < 355 then 43 else 10))) else (if i.val < 360 then (if i.val < 358 then (if i.val < 357 then 9 else 9) else (if i.val < 359 then 9 else 91)) else (if i.val < 362 then (if i.val < 361 then 9 else 91) else (if i.val < 363 then 42 else 51))))))) else (if i.val < 425 then (if i.val < 394 then (if i.val < 379 then (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then 14 else (if i.val < 366 then 81 else 14)) else (if i.val < 369 then (if i.val < 368 then 14 else 77) else (if i.val < 370 then 14 else 71))) else (if i.val < 375 then (if i.val < 373 then (if i.val < 372 then 82 else 14) else (if i.val < 374 then 71 else 77)) else (if i.val < 377 then (if i.val < 376 then 74 else 51) else (if i.val < 378 then 4 else 35)))) else (if i.val < 386 then (if i.val < 382 then (if i.val < 380 then 77 else (if i.val < 381 then 71 else 77)) else (if i.val < 384 then (if i.val < 383 then 71 else 82) else (if i.val < 385 then 4 else 77))) else (if i.val < 390 then (if i.val < 388 then (if i.val < 387 then 77 else 100) else (if i.val < 389 then 45 else 51)) else (if i.val < 392 then (if i.val < 391 then 14 else 14) else (if i.val < 393 then 71 else 77))))) else (if i.val < 409 then (if i.val < 401 then (if i.val < 397 then (if i.val < 395 then 71 else (if i.val < 396 then 77 else 45)) else (if i.val < 399 then (if i.val < 398 then 45 else 14) else (if i.val < 400 then 77 else 14))) else (if i.val < 405 then (if i.val < 403 then (if i.val < 402 then 35 else 71) else (if i.val < 404 then 81 else 35)) else (if i.val < 407 then (if i.val < 406 then 45 else 45) else (if i.val < 408 then 29 else 3)))) else (if i.val < 417 then (if i.val < 413 then (if i.val < 411 then (if i.val < 410 then 14 else 45) else (if i.val < 412 then 3 else 14)) else (if i.val < 415 then (if i.val < 414 then 71 else 14) else (if i.val < 416 then 3 else 3))) else (if i.val < 421 then (if i.val < 419 then (if i.val < 418 then 42 else 3) else (if i.val < 420 then 42 else 71)) else (if i.val < 423 then (if i.val < 422 then 51 else 4) else (if i.val < 424 then 74 else 3)))))) else (if i.val < 455 then (if i.val < 440 then (if i.val < 432 then (if i.val < 428 then (if i.val < 426 then 42 else (if i.val < 427 then 78 else 4)) else (if i.val < 430 then (if i.val < 429 then 19 else 19) else (if i.val < 431 then 45 else 100))) else (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then 54 else 54) else (if i.val < 435 then 19 else 100)) else (if i.val < 438 then (if i.val < 437 then 54 else 66) else (if i.val < 439 then 4 else 19)))) else (if i.val < 447 then (if i.val < 443 then (if i.val < 441 then 54 else (if i.val < 442 then 45 else 100)) else (if i.val < 445 then (if i.val < 444 then 54 else 64) else (if i.val < 446 then 64 else 19))) else (if i.val < 451 then (if i.val < 449 then (if i.val < 448 then 54 else 19) else (if i.val < 450 then 54 else 64)) else (if i.val < 453 then (if i.val < 452 then 64 else 67) else (if i.val < 454 then 19 else 19))))) else (if i.val < 470 then (if i.val < 462 then (if i.val < 458 then (if i.val < 456 then 54 else (if i.val < 457 then 19 else 85)) else (if i.val < 460 then (if i.val < 459 then 6 else 54) else (if i.val < 461 then 45 else 6))) else (if i.val < 466 then (if i.val < 464 then (if i.val < 463 then 85 else 86) else (if i.val < 465 then 59 else 4)) else (if i.val < 468 then (if i.val < 467 then 9 else 91) else (if i.val < 469 then 65 else 89)))) else (if i.val < 478 then (if i.val < 474 then (if i.val < 472 then (if i.val < 471 then 89 else 6) else (if i.val < 473 then 89 else 68)) else (if i.val < 476 then (if i.val < 475 then 6 else 10) else (if i.val < 477 then 9 else 91))) else (if i.val < 482 then (if i.val < 480 then (if i.val < 479 then 91 else 35) else (if i.val < 481 then 87 else 6)) else (if i.val < 484 then (if i.val < 483 then 40 else 82) else (if i.val < 485 then 81 else 1)))))))))

def g32p_supplierGroup03_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 14, 15, 18, 19, 23, 25, 29, 35, 36, 40, 42, 43, 45, 50, 51, 54, 59, 64, 65, 66, 67, 68, 71, 74, 76, 77, 78, 79, 81, 82, 85, 86, 87, 89, 91, 96, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup03_matrix_000 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 0 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 0 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 0 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 0 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 0 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_001 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 1 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 1 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 1 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 1 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 1 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_002 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 2 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 2 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 2 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 2 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 2 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_003 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 3 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 3 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 3 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 3 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 3 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_004 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 4 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 4 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 4 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 4 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 4 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_005 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 5 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 5 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 5 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 5 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 5 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_006 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 6 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 6 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 6 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 6 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 6 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_007 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 7 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 7 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 7 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 7 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 7 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_008 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 8 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 8 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 8 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 8 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 8 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_009 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 9 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 9 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 9 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 9 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 9 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_010 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 10 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 10 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 10 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 10 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 10 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_011 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 11 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 11 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 11 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 11 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 11 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_012 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 12 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 12 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 12 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 12 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 12 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_013 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 13 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 13 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 13 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 13 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 13 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_014 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 14 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 14 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 14 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 14 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 14 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_015 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 15 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 15 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 15 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 15 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 15 r) ∈ g32p_supplierGroup03_support := by
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

theorem g32p_supplierGroup03_matrix_016 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 16 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 16 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 16 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 16 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 16 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_017 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 17 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 17 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 17 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 17 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 17 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_018 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 18 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 18 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 18 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 18 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 18 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_019 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 19 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 19 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 19 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 19 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 19 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_020 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 20 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 20 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 20 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 20 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 20 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_021 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 21 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 21 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 21 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 21 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 21 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_022 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 22 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 22 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 22 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 22 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 22 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_023 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 23 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 23 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 23 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 23 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 23 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_024 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 24 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 24 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 24 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 24 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 24 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_025 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 25 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 25 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 25 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 25 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 25 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_026 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 26 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 26 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 26 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 26 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 26 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_027 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 27 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 27 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 27 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 27 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 27 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_028 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 28 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 28 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 28 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 28 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 28 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_029 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 29 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 29 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 29 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 29 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 29 r) ∈ g32p_supplierGroup03_support := by
  decide +kernel

theorem g32p_supplierGroup03_matrix_030 : ∀ r : Fin 16,
    g32p_row05_groupNodes (g32p_finBlockIndex 486 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 30 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup03_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup03_source (g32p_finBlockIndex 486 30 r)).1 (g32p_supplierGroup03_source (g32p_finBlockIndex 486 30 r)).2 =
      g32p_supplierGroup03_classify (g32p_finBlockIndex 486 30 r) := by
  decide +kernel

theorem g32p_supplierGroup03_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup03_classify (g32p_finBlockIndex 486 30 r) ∈ g32p_supplierGroup03_support := by
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

theorem g32p_supplierGroup03_matrix (i : Fin 486) :
    g32p_row05_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source i).1 (g32p_supplierGroup03_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row05_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup03_source i).1 (g32p_supplierGroup03_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup03_matrix_000 r
  · exact g32p_supplierGroup03_matrix_001 r
  · exact g32p_supplierGroup03_matrix_002 r
  · exact g32p_supplierGroup03_matrix_003 r
  · exact g32p_supplierGroup03_matrix_004 r
  · exact g32p_supplierGroup03_matrix_005 r
  · exact g32p_supplierGroup03_matrix_006 r
  · exact g32p_supplierGroup03_matrix_007 r
  · exact g32p_supplierGroup03_matrix_008 r
  · exact g32p_supplierGroup03_matrix_009 r
  · exact g32p_supplierGroup03_matrix_010 r
  · exact g32p_supplierGroup03_matrix_011 r
  · exact g32p_supplierGroup03_matrix_012 r
  · exact g32p_supplierGroup03_matrix_013 r
  · exact g32p_supplierGroup03_matrix_014 r
  · exact g32p_supplierGroup03_matrix_015 r
  · exact g32p_supplierGroup03_matrix_016 r
  · exact g32p_supplierGroup03_matrix_017 r
  · exact g32p_supplierGroup03_matrix_018 r
  · exact g32p_supplierGroup03_matrix_019 r
  · exact g32p_supplierGroup03_matrix_020 r
  · exact g32p_supplierGroup03_matrix_021 r
  · exact g32p_supplierGroup03_matrix_022 r
  · exact g32p_supplierGroup03_matrix_023 r
  · exact g32p_supplierGroup03_matrix_024 r
  · exact g32p_supplierGroup03_matrix_025 r
  · exact g32p_supplierGroup03_matrix_026 r
  · exact g32p_supplierGroup03_matrix_027 r
  · exact g32p_supplierGroup03_matrix_028 r
  · exact g32p_supplierGroup03_matrix_029 r
  · exact g32p_supplierGroup03_matrix_030 r

theorem g32p_supplierGroup03_class (i : Fin 486) :
    g32p_supplierForest_classes (g32p_supplierGroup03_source i).1 (g32p_supplierGroup03_source i).2 =
      g32p_supplierGroup03_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup03_source i).1 (g32p_supplierGroup03_source i).2 =
      g32p_supplierGroup03_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup03_class_000 r
  · exact g32p_supplierGroup03_class_001 r
  · exact g32p_supplierGroup03_class_002 r
  · exact g32p_supplierGroup03_class_003 r
  · exact g32p_supplierGroup03_class_004 r
  · exact g32p_supplierGroup03_class_005 r
  · exact g32p_supplierGroup03_class_006 r
  · exact g32p_supplierGroup03_class_007 r
  · exact g32p_supplierGroup03_class_008 r
  · exact g32p_supplierGroup03_class_009 r
  · exact g32p_supplierGroup03_class_010 r
  · exact g32p_supplierGroup03_class_011 r
  · exact g32p_supplierGroup03_class_012 r
  · exact g32p_supplierGroup03_class_013 r
  · exact g32p_supplierGroup03_class_014 r
  · exact g32p_supplierGroup03_class_015 r
  · exact g32p_supplierGroup03_class_016 r
  · exact g32p_supplierGroup03_class_017 r
  · exact g32p_supplierGroup03_class_018 r
  · exact g32p_supplierGroup03_class_019 r
  · exact g32p_supplierGroup03_class_020 r
  · exact g32p_supplierGroup03_class_021 r
  · exact g32p_supplierGroup03_class_022 r
  · exact g32p_supplierGroup03_class_023 r
  · exact g32p_supplierGroup03_class_024 r
  · exact g32p_supplierGroup03_class_025 r
  · exact g32p_supplierGroup03_class_026 r
  · exact g32p_supplierGroup03_class_027 r
  · exact g32p_supplierGroup03_class_028 r
  · exact g32p_supplierGroup03_class_029 r
  · exact g32p_supplierGroup03_class_030 r

theorem g32p_supplierGroup03_support_mem (i : Fin 486) :
    g32p_supplierGroup03_classify i ∈ g32p_supplierGroup03_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup03_classify i ∈ g32p_supplierGroup03_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup03_support_000 r
  · exact g32p_supplierGroup03_support_001 r
  · exact g32p_supplierGroup03_support_002 r
  · exact g32p_supplierGroup03_support_003 r
  · exact g32p_supplierGroup03_support_004 r
  · exact g32p_supplierGroup03_support_005 r
  · exact g32p_supplierGroup03_support_006 r
  · exact g32p_supplierGroup03_support_007 r
  · exact g32p_supplierGroup03_support_008 r
  · exact g32p_supplierGroup03_support_009 r
  · exact g32p_supplierGroup03_support_010 r
  · exact g32p_supplierGroup03_support_011 r
  · exact g32p_supplierGroup03_support_012 r
  · exact g32p_supplierGroup03_support_013 r
  · exact g32p_supplierGroup03_support_014 r
  · exact g32p_supplierGroup03_support_015 r
  · exact g32p_supplierGroup03_support_016 r
  · exact g32p_supplierGroup03_support_017 r
  · exact g32p_supplierGroup03_support_018 r
  · exact g32p_supplierGroup03_support_019 r
  · exact g32p_supplierGroup03_support_020 r
  · exact g32p_supplierGroup03_support_021 r
  · exact g32p_supplierGroup03_support_022 r
  · exact g32p_supplierGroup03_support_023 r
  · exact g32p_supplierGroup03_support_024 r
  · exact g32p_supplierGroup03_support_025 r
  · exact g32p_supplierGroup03_support_026 r
  · exact g32p_supplierGroup03_support_027 r
  · exact g32p_supplierGroup03_support_028 r
  · exact g32p_supplierGroup03_support_029 r
  · exact g32p_supplierGroup03_support_030 r

end HodgeLean.Foundations.Program

end
end
