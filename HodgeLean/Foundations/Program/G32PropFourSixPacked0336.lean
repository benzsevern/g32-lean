import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_005 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 5 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_005_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 13 14, g32p_row04_traceSegment_005_0000_0013, g32p_row04_traceSegment_005_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 27 13 14, g32p_row04_traceSegment_005_0027_0013, g32p_row04_traceSegment_005_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 27 27, g32p_row04_traceSegment_005_0000_0027, g32p_row04_traceSegment_005_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 54 13 14, g32p_row04_traceSegment_005_0054_0013, g32p_row04_traceSegment_005_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 81 13 14, g32p_row04_traceSegment_005_0081_0013, g32p_row04_traceSegment_005_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 54 27 27, g32p_row04_traceSegment_005_0054_0027, g32p_row04_traceSegment_005_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 54 54, g32p_row04_traceSegment_005_0000_0054, g32p_row04_traceSegment_005_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 108 13 14, g32p_row04_traceSegment_005_0108_0013, g32p_row04_traceSegment_005_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 135 13 14, g32p_row04_traceSegment_005_0135_0013, g32p_row04_traceSegment_005_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 108 27 27, g32p_row04_traceSegment_005_0108_0027, g32p_row04_traceSegment_005_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 162 13 14, g32p_row04_traceSegment_005_0162_0013, g32p_row04_traceSegment_005_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 189 13 14, g32p_row04_traceSegment_005_0189_0013, g32p_row04_traceSegment_005_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 162 27 27, g32p_row04_traceSegment_005_0162_0027, g32p_row04_traceSegment_005_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 108 54 54, g32p_row04_traceSegment_005_0108_0054, g32p_row04_traceSegment_005_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 108 108, g32p_row04_traceSegment_005_0000_0108, g32p_row04_traceSegment_005_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 216 13 14, g32p_row04_traceSegment_005_0216_0013, g32p_row04_traceSegment_005_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 243 13 14, g32p_row04_traceSegment_005_0243_0013, g32p_row04_traceSegment_005_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 216 27 27, g32p_row04_traceSegment_005_0216_0027, g32p_row04_traceSegment_005_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 270 13 14, g32p_row04_traceSegment_005_0270_0013, g32p_row04_traceSegment_005_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 297 13 14, g32p_row04_traceSegment_005_0297_0013, g32p_row04_traceSegment_005_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 270 27 27, g32p_row04_traceSegment_005_0270_0027, g32p_row04_traceSegment_005_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 216 54 54, g32p_row04_traceSegment_005_0216_0054, g32p_row04_traceSegment_005_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 324 13 14, g32p_row04_traceSegment_005_0324_0013, g32p_row04_traceSegment_005_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 351 13 14, g32p_row04_traceSegment_005_0351_0013, g32p_row04_traceSegment_005_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 324 27 27, g32p_row04_traceSegment_005_0324_0027, g32p_row04_traceSegment_005_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 378 13 14, g32p_row04_traceSegment_005_0378_0013, g32p_row04_traceSegment_005_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 405 13 14, g32p_row04_traceSegment_005_0405_0013, g32p_row04_traceSegment_005_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 378 27 27, g32p_row04_traceSegment_005_0378_0027, g32p_row04_traceSegment_005_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 324 54 54, g32p_row04_traceSegment_005_0324_0054, g32p_row04_traceSegment_005_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 216 108 108, g32p_row04_traceSegment_005_0216_0108, g32p_row04_traceSegment_005_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_005 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 216 216, g32p_row04_traceSegment_005_0000_0216, g32p_row04_traceSegment_005_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 432 13 14, g32p_row04_traceSegment_005_0432_0013, g32p_row04_traceSegment_005_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 459 13 14, g32p_row04_traceSegment_005_0459_0013, g32p_row04_traceSegment_005_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 432 27 27, g32p_row04_traceSegment_005_0432_0027, g32p_row04_traceSegment_005_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 486 13 14, g32p_row04_traceSegment_005_0486_0013, g32p_row04_traceSegment_005_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 513 13 14, g32p_row04_traceSegment_005_0513_0013, g32p_row04_traceSegment_005_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 486 27 27, g32p_row04_traceSegment_005_0486_0027, g32p_row04_traceSegment_005_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 432 54 54, g32p_row04_traceSegment_005_0432_0054, g32p_row04_traceSegment_005_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 540 13 14, g32p_row04_traceSegment_005_0540_0013, g32p_row04_traceSegment_005_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 567 13 14, g32p_row04_traceSegment_005_0567_0013, g32p_row04_traceSegment_005_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 540 27 27, g32p_row04_traceSegment_005_0540_0027, g32p_row04_traceSegment_005_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 594 13 14, g32p_row04_traceSegment_005_0594_0013, g32p_row04_traceSegment_005_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 621 13 14, g32p_row04_traceSegment_005_0621_0013, g32p_row04_traceSegment_005_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 594 27 27, g32p_row04_traceSegment_005_0594_0027, g32p_row04_traceSegment_005_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 540 54 54, g32p_row04_traceSegment_005_0540_0054, g32p_row04_traceSegment_005_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 432 108 108, g32p_row04_traceSegment_005_0432_0108, g32p_row04_traceSegment_005_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 648 13 14, g32p_row04_traceSegment_005_0648_0013, g32p_row04_traceSegment_005_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 675 13 14, g32p_row04_traceSegment_005_0675_0013, g32p_row04_traceSegment_005_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 648 27 27, g32p_row04_traceSegment_005_0648_0027, g32p_row04_traceSegment_005_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 702 13 14, g32p_row04_traceSegment_005_0702_0013, g32p_row04_traceSegment_005_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 729 13 14, g32p_row04_traceSegment_005_0729_0013, g32p_row04_traceSegment_005_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 702 27 27, g32p_row04_traceSegment_005_0702_0027, g32p_row04_traceSegment_005_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 648 54 54, g32p_row04_traceSegment_005_0648_0054, g32p_row04_traceSegment_005_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 756 13 14, g32p_row04_traceSegment_005_0756_0013, g32p_row04_traceSegment_005_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 783 13 14, g32p_row04_traceSegment_005_0783_0013, g32p_row04_traceSegment_005_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 756 27 27, g32p_row04_traceSegment_005_0756_0027, g32p_row04_traceSegment_005_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 810 13 14, g32p_row04_traceSegment_005_0810_0013, g32p_row04_traceSegment_005_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 837 13 14, g32p_row04_traceSegment_005_0837_0013, g32p_row04_traceSegment_005_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 810 27 27, g32p_row04_traceSegment_005_0810_0027, g32p_row04_traceSegment_005_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 756 54 54, g32p_row04_traceSegment_005_0756_0054, g32p_row04_traceSegment_005_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 648 108 108, g32p_row04_traceSegment_005_0648_0108, g32p_row04_traceSegment_005_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_005 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 432 216 216, g32p_row04_traceSegment_005_0432_0216, g32p_row04_traceSegment_005_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_005 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 432 432, g32p_row04_traceSegment_005_0000_0432, g32p_row04_traceSegment_005_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 864 13 14, g32p_row04_traceSegment_005_0864_0013, g32p_row04_traceSegment_005_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 891 13 14, g32p_row04_traceSegment_005_0891_0013, g32p_row04_traceSegment_005_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 864 27 27, g32p_row04_traceSegment_005_0864_0027, g32p_row04_traceSegment_005_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 918 13 14, g32p_row04_traceSegment_005_0918_0013, g32p_row04_traceSegment_005_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 945 13 14, g32p_row04_traceSegment_005_0945_0013, g32p_row04_traceSegment_005_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 918 27 27, g32p_row04_traceSegment_005_0918_0027, g32p_row04_traceSegment_005_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 864 54 54, g32p_row04_traceSegment_005_0864_0054, g32p_row04_traceSegment_005_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 972 13 14, g32p_row04_traceSegment_005_0972_0013, g32p_row04_traceSegment_005_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1012 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 999 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 999 13 14, g32p_row04_traceSegment_005_0999_0013, g32p_row04_traceSegment_005_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 972 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 972 27 27, g32p_row04_traceSegment_005_0972_0027, g32p_row04_traceSegment_005_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1026 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1039 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1026 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1026 13 14, g32p_row04_traceSegment_005_1026_0013, g32p_row04_traceSegment_005_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1053 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1066 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1053 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1053 13 14, g32p_row04_traceSegment_005_1053_0013, g32p_row04_traceSegment_005_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1026 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1026 27 27, g32p_row04_traceSegment_005_1026_0027, g32p_row04_traceSegment_005_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 972 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 972 54 54, g32p_row04_traceSegment_005_0972_0054, g32p_row04_traceSegment_005_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 864 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 864 108 108, g32p_row04_traceSegment_005_0864_0108, g32p_row04_traceSegment_005_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1080 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1080 13 14, g32p_row04_traceSegment_005_1080_0013, g32p_row04_traceSegment_005_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1107 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1107 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1107 13 14, g32p_row04_traceSegment_005_1107_0013, g32p_row04_traceSegment_005_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1080 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1080 27 27, g32p_row04_traceSegment_005_1080_0027, g32p_row04_traceSegment_005_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1147 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1134 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1134 13 14, g32p_row04_traceSegment_005_1134_0013, g32p_row04_traceSegment_005_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1161 13 14, g32p_row04_traceSegment_005_1161_0013, g32p_row04_traceSegment_005_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1134 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1134 27 27, g32p_row04_traceSegment_005_1134_0027, g32p_row04_traceSegment_005_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 1080 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1080 54 54, g32p_row04_traceSegment_005_1080_0054, g32p_row04_traceSegment_005_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1188 13 14, g32p_row04_traceSegment_005_1188_0013, g32p_row04_traceSegment_005_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1215 13 14, g32p_row04_traceSegment_005_1215_0013, g32p_row04_traceSegment_005_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1188 27 27, g32p_row04_traceSegment_005_1188_0027, g32p_row04_traceSegment_005_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1242 13 14, g32p_row04_traceSegment_005_1242_0013, g32p_row04_traceSegment_005_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1269 13 14, g32p_row04_traceSegment_005_1269_0013, g32p_row04_traceSegment_005_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1242 27 27, g32p_row04_traceSegment_005_1242_0027, g32p_row04_traceSegment_005_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1188 54 54, g32p_row04_traceSegment_005_1188_0054, g32p_row04_traceSegment_005_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 1080 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1080 108 108, g32p_row04_traceSegment_005_1080_0108, g32p_row04_traceSegment_005_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_005 864 432 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 864 216 216, g32p_row04_traceSegment_005_0864_0216, g32p_row04_traceSegment_005_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1296 13 14, g32p_row04_traceSegment_005_1296_0013, g32p_row04_traceSegment_005_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1323 13 14, g32p_row04_traceSegment_005_1323_0013, g32p_row04_traceSegment_005_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1296 27 27, g32p_row04_traceSegment_005_1296_0027, g32p_row04_traceSegment_005_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1350 13 14, g32p_row04_traceSegment_005_1350_0013, g32p_row04_traceSegment_005_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1377 13 14, g32p_row04_traceSegment_005_1377_0013, g32p_row04_traceSegment_005_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1350 27 27, g32p_row04_traceSegment_005_1350_0027, g32p_row04_traceSegment_005_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1296 54 54, g32p_row04_traceSegment_005_1296_0054, g32p_row04_traceSegment_005_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1404 13 14, g32p_row04_traceSegment_005_1404_0013, g32p_row04_traceSegment_005_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1431 13 14, g32p_row04_traceSegment_005_1431_0013, g32p_row04_traceSegment_005_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1404 27 27, g32p_row04_traceSegment_005_1404_0027, g32p_row04_traceSegment_005_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1458 13 14, g32p_row04_traceSegment_005_1458_0013, g32p_row04_traceSegment_005_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1485 13 14, g32p_row04_traceSegment_005_1485_0013, g32p_row04_traceSegment_005_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1458 27 27, g32p_row04_traceSegment_005_1458_0027, g32p_row04_traceSegment_005_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1404 54 54, g32p_row04_traceSegment_005_1404_0054, g32p_row04_traceSegment_005_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1296 108 108, g32p_row04_traceSegment_005_1296_0108, g32p_row04_traceSegment_005_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1512 13 14, g32p_row04_traceSegment_005_1512_0013, g32p_row04_traceSegment_005_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1539 13 14, g32p_row04_traceSegment_005_1539_0013, g32p_row04_traceSegment_005_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1512 27 27, g32p_row04_traceSegment_005_1512_0027, g32p_row04_traceSegment_005_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1566 13 14, g32p_row04_traceSegment_005_1566_0013, g32p_row04_traceSegment_005_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1593 13 14, g32p_row04_traceSegment_005_1593_0013, g32p_row04_traceSegment_005_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1566 27 27, g32p_row04_traceSegment_005_1566_0027, g32p_row04_traceSegment_005_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1512 54 54, g32p_row04_traceSegment_005_1512_0054, g32p_row04_traceSegment_005_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1620 13 14, g32p_row04_traceSegment_005_1620_0013, g32p_row04_traceSegment_005_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1647 13 14, g32p_row04_traceSegment_005_1647_0013, g32p_row04_traceSegment_005_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1620 27 27, g32p_row04_traceSegment_005_1620_0027, g32p_row04_traceSegment_005_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1674 13 14, g32p_row04_traceSegment_005_1674_0013, g32p_row04_traceSegment_005_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_005 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_005 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_005_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_005 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1701 13 14, g32p_row04_traceSegment_005_1701_0013, g32p_row04_traceSegment_005_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_005 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1674 27 27, g32p_row04_traceSegment_005_1674_0027, g32p_row04_traceSegment_005_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_005 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1620 54 54, g32p_row04_traceSegment_005_1620_0054, g32p_row04_traceSegment_005_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_005 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1512 108 108, g32p_row04_traceSegment_005_1512_0108, g32p_row04_traceSegment_005_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_005_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_005 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 1296 216 216, g32p_row04_traceSegment_005_1296_0216, g32p_row04_traceSegment_005_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_005 864 864 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 864 432 432, g32p_row04_traceSegment_005_0864_0432, g32p_row04_traceSegment_005_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_005_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_005 0 1728 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_005 0 864 864, g32p_row04_traceSegment_005_0000_0864, g32p_row04_traceSegment_005_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 5 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_005_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_006_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 13 14, g32p_row04_traceSegment_006_0000_0013, g32p_row04_traceSegment_006_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 27 13 14, g32p_row04_traceSegment_006_0027_0013, g32p_row04_traceSegment_006_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 27 27, g32p_row04_traceSegment_006_0000_0027, g32p_row04_traceSegment_006_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 54 13 14, g32p_row04_traceSegment_006_0054_0013, g32p_row04_traceSegment_006_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 81 13 14, g32p_row04_traceSegment_006_0081_0013, g32p_row04_traceSegment_006_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 54 27 27, g32p_row04_traceSegment_006_0054_0027, g32p_row04_traceSegment_006_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 54 54, g32p_row04_traceSegment_006_0000_0054, g32p_row04_traceSegment_006_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 108 13 14, g32p_row04_traceSegment_006_0108_0013, g32p_row04_traceSegment_006_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 135 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 148 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 135 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 135 13 14, g32p_row04_traceSegment_006_0135_0013, g32p_row04_traceSegment_006_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 108 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 108 27 27, g32p_row04_traceSegment_006_0108_0027, g32p_row04_traceSegment_006_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 162 13 14, g32p_row04_traceSegment_006_0162_0013, g32p_row04_traceSegment_006_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 202 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 189 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 189 13 14, g32p_row04_traceSegment_006_0189_0013, g32p_row04_traceSegment_006_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 162 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 162 27 27, g32p_row04_traceSegment_006_0162_0027, g32p_row04_traceSegment_006_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 108 108 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 108 54 54, g32p_row04_traceSegment_006_0108_0054, g32p_row04_traceSegment_006_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 0 216 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 108 108, g32p_row04_traceSegment_006_0000_0108, g32p_row04_traceSegment_006_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 216 13 14, g32p_row04_traceSegment_006_0216_0013, g32p_row04_traceSegment_006_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 256 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 243 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 243 13 14, g32p_row04_traceSegment_006_0243_0013, g32p_row04_traceSegment_006_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 216 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 216 27 27, g32p_row04_traceSegment_006_0216_0027, g32p_row04_traceSegment_006_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 270 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 270 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 270 13 14, g32p_row04_traceSegment_006_0270_0013, g32p_row04_traceSegment_006_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 297 13 14, g32p_row04_traceSegment_006_0297_0013, g32p_row04_traceSegment_006_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 270 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 270 27 27, g32p_row04_traceSegment_006_0270_0027, g32p_row04_traceSegment_006_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 216 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 216 54 54, g32p_row04_traceSegment_006_0216_0054, g32p_row04_traceSegment_006_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 324 13 14, g32p_row04_traceSegment_006_0324_0013, g32p_row04_traceSegment_006_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 351 13 14, g32p_row04_traceSegment_006_0351_0013, g32p_row04_traceSegment_006_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 324 27 27, g32p_row04_traceSegment_006_0324_0027, g32p_row04_traceSegment_006_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 378 13 14, g32p_row04_traceSegment_006_0378_0013, g32p_row04_traceSegment_006_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 405 13 14, g32p_row04_traceSegment_006_0405_0013, g32p_row04_traceSegment_006_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 378 27 27, g32p_row04_traceSegment_006_0378_0027, g32p_row04_traceSegment_006_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 324 54 54, g32p_row04_traceSegment_006_0324_0054, g32p_row04_traceSegment_006_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 216 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 216 108 108, g32p_row04_traceSegment_006_0216_0108, g32p_row04_traceSegment_006_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_006 0 432 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 216 216, g32p_row04_traceSegment_006_0000_0216, g32p_row04_traceSegment_006_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 432 13 14, g32p_row04_traceSegment_006_0432_0013, g32p_row04_traceSegment_006_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 459 13 14, g32p_row04_traceSegment_006_0459_0013, g32p_row04_traceSegment_006_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 432 27 27, g32p_row04_traceSegment_006_0432_0027, g32p_row04_traceSegment_006_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 486 13 14, g32p_row04_traceSegment_006_0486_0013, g32p_row04_traceSegment_006_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 513 13 14, g32p_row04_traceSegment_006_0513_0013, g32p_row04_traceSegment_006_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 486 27 27, g32p_row04_traceSegment_006_0486_0027, g32p_row04_traceSegment_006_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 432 54 54, g32p_row04_traceSegment_006_0432_0054, g32p_row04_traceSegment_006_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 540 13 14, g32p_row04_traceSegment_006_0540_0013, g32p_row04_traceSegment_006_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 567 13 14, g32p_row04_traceSegment_006_0567_0013, g32p_row04_traceSegment_006_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 540 27 27, g32p_row04_traceSegment_006_0540_0027, g32p_row04_traceSegment_006_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 594 13 14, g32p_row04_traceSegment_006_0594_0013, g32p_row04_traceSegment_006_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 621 13 14, g32p_row04_traceSegment_006_0621_0013, g32p_row04_traceSegment_006_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 594 27 27, g32p_row04_traceSegment_006_0594_0027, g32p_row04_traceSegment_006_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 540 54 54, g32p_row04_traceSegment_006_0540_0054, g32p_row04_traceSegment_006_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 432 108 108, g32p_row04_traceSegment_006_0432_0108, g32p_row04_traceSegment_006_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 648 13 14, g32p_row04_traceSegment_006_0648_0013, g32p_row04_traceSegment_006_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 675 13 14, g32p_row04_traceSegment_006_0675_0013, g32p_row04_traceSegment_006_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 648 27 27, g32p_row04_traceSegment_006_0648_0027, g32p_row04_traceSegment_006_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 702 13 14, g32p_row04_traceSegment_006_0702_0013, g32p_row04_traceSegment_006_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 729 13 14, g32p_row04_traceSegment_006_0729_0013, g32p_row04_traceSegment_006_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 702 27 27, g32p_row04_traceSegment_006_0702_0027, g32p_row04_traceSegment_006_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 648 54 54, g32p_row04_traceSegment_006_0648_0054, g32p_row04_traceSegment_006_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 756 13 14, g32p_row04_traceSegment_006_0756_0013, g32p_row04_traceSegment_006_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 783 13 14, g32p_row04_traceSegment_006_0783_0013, g32p_row04_traceSegment_006_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 756 27 27, g32p_row04_traceSegment_006_0756_0027, g32p_row04_traceSegment_006_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 823 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 810 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 810 13 14, g32p_row04_traceSegment_006_0810_0013, g32p_row04_traceSegment_006_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 837 13 14, g32p_row04_traceSegment_006_0837_0013, g32p_row04_traceSegment_006_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 810 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 810 27 27, g32p_row04_traceSegment_006_0810_0027, g32p_row04_traceSegment_006_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 756 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 756 54 54, g32p_row04_traceSegment_006_0756_0054, g32p_row04_traceSegment_006_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 648 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 648 108 108, g32p_row04_traceSegment_006_0648_0108, g32p_row04_traceSegment_006_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_006 432 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 432 216 216, g32p_row04_traceSegment_006_0432_0216, g32p_row04_traceSegment_006_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_006 0 864 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 432 432, g32p_row04_traceSegment_006_0000_0432, g32p_row04_traceSegment_006_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 864 13 14, g32p_row04_traceSegment_006_0864_0013, g32p_row04_traceSegment_006_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 891 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 891 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 891 13 14, g32p_row04_traceSegment_006_0891_0013, g32p_row04_traceSegment_006_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 864 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 864 27 27, g32p_row04_traceSegment_006_0864_0027, g32p_row04_traceSegment_006_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 931 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 918 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 918 13 14, g32p_row04_traceSegment_006_0918_0013, g32p_row04_traceSegment_006_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 945 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 945 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 945 13 14, g32p_row04_traceSegment_006_0945_0013, g32p_row04_traceSegment_006_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 918 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 918 27 27, g32p_row04_traceSegment_006_0918_0027, g32p_row04_traceSegment_006_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 864 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 864 54 54, g32p_row04_traceSegment_006_0864_0054, g32p_row04_traceSegment_006_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 972 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 985 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 972 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 972 13 14, g32p_row04_traceSegment_006_0972_0013, g32p_row04_traceSegment_006_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 999 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1012 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 999 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 999 13 14, g32p_row04_traceSegment_006_0999_0013, g32p_row04_traceSegment_006_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 972 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 972 27 27, g32p_row04_traceSegment_006_0972_0027, g32p_row04_traceSegment_006_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1039 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1026 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1026 13 14, g32p_row04_traceSegment_006_1026_0013, g32p_row04_traceSegment_006_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1053 13 14, g32p_row04_traceSegment_006_1053_0013, g32p_row04_traceSegment_006_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1026 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1026 27 27, g32p_row04_traceSegment_006_1026_0027, g32p_row04_traceSegment_006_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 972 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 972 54 54, g32p_row04_traceSegment_006_0972_0054, g32p_row04_traceSegment_006_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 864 216 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 864 108 108, g32p_row04_traceSegment_006_0864_0108, g32p_row04_traceSegment_006_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1093 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1080 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1080 13 14, g32p_row04_traceSegment_006_1080_0013, g32p_row04_traceSegment_006_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1107 13 14, g32p_row04_traceSegment_006_1107_0013, g32p_row04_traceSegment_006_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1080 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1080 27 27, g32p_row04_traceSegment_006_1080_0027, g32p_row04_traceSegment_006_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1147 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1134 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1134 13 14, g32p_row04_traceSegment_006_1134_0013, g32p_row04_traceSegment_006_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1161 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1174 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1161 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1161 13 14, g32p_row04_traceSegment_006_1161_0013, g32p_row04_traceSegment_006_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1134 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1134 27 27, g32p_row04_traceSegment_006_1134_0027, g32p_row04_traceSegment_006_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 1080 108 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1080 54 54, g32p_row04_traceSegment_006_1080_0054, g32p_row04_traceSegment_006_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1188 13 14, g32p_row04_traceSegment_006_1188_0013, g32p_row04_traceSegment_006_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1215 13 14, g32p_row04_traceSegment_006_1215_0013, g32p_row04_traceSegment_006_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1188 27 27, g32p_row04_traceSegment_006_1188_0027, g32p_row04_traceSegment_006_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1242 13 14, g32p_row04_traceSegment_006_1242_0013, g32p_row04_traceSegment_006_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1269 13 14, g32p_row04_traceSegment_006_1269_0013, g32p_row04_traceSegment_006_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1242 27 27, g32p_row04_traceSegment_006_1242_0027, g32p_row04_traceSegment_006_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1188 54 54, g32p_row04_traceSegment_006_1188_0054, g32p_row04_traceSegment_006_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 1080 216 = [0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1080 108 108, g32p_row04_traceSegment_006_1080_0108, g32p_row04_traceSegment_006_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_006 864 432 = [0, 14, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 864 216 216, g32p_row04_traceSegment_006_0864_0216, g32p_row04_traceSegment_006_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1296 13 14, g32p_row04_traceSegment_006_1296_0013, g32p_row04_traceSegment_006_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1323 13 14, g32p_row04_traceSegment_006_1323_0013, g32p_row04_traceSegment_006_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1296 27 27, g32p_row04_traceSegment_006_1296_0027, g32p_row04_traceSegment_006_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1350 13 14, g32p_row04_traceSegment_006_1350_0013, g32p_row04_traceSegment_006_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1377 13 14, g32p_row04_traceSegment_006_1377_0013, g32p_row04_traceSegment_006_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1350 27 27, g32p_row04_traceSegment_006_1350_0027, g32p_row04_traceSegment_006_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1296 54 54, g32p_row04_traceSegment_006_1296_0054, g32p_row04_traceSegment_006_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1404 13 14, g32p_row04_traceSegment_006_1404_0013, g32p_row04_traceSegment_006_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1431 13 14, g32p_row04_traceSegment_006_1431_0013, g32p_row04_traceSegment_006_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1404 27 27, g32p_row04_traceSegment_006_1404_0027, g32p_row04_traceSegment_006_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1458 13 14, g32p_row04_traceSegment_006_1458_0013, g32p_row04_traceSegment_006_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1485 13 14, g32p_row04_traceSegment_006_1485_0013, g32p_row04_traceSegment_006_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1458 27 27, g32p_row04_traceSegment_006_1458_0027, g32p_row04_traceSegment_006_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1404 54 54, g32p_row04_traceSegment_006_1404_0054, g32p_row04_traceSegment_006_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1296 108 108, g32p_row04_traceSegment_006_1296_0108, g32p_row04_traceSegment_006_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1512 13 14, g32p_row04_traceSegment_006_1512_0013, g32p_row04_traceSegment_006_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1539 13 14, g32p_row04_traceSegment_006_1539_0013, g32p_row04_traceSegment_006_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1512 27 27, g32p_row04_traceSegment_006_1512_0027, g32p_row04_traceSegment_006_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1566 13 14, g32p_row04_traceSegment_006_1566_0013, g32p_row04_traceSegment_006_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1593 13 14, g32p_row04_traceSegment_006_1593_0013, g32p_row04_traceSegment_006_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1566 27 27, g32p_row04_traceSegment_006_1566_0027, g32p_row04_traceSegment_006_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1512 54 54, g32p_row04_traceSegment_006_1512_0054, g32p_row04_traceSegment_006_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1620 13 14, g32p_row04_traceSegment_006_1620_0013, g32p_row04_traceSegment_006_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1647 13 14, g32p_row04_traceSegment_006_1647_0013, g32p_row04_traceSegment_006_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1620 27 27, g32p_row04_traceSegment_006_1620_0027, g32p_row04_traceSegment_006_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1674 13 14, g32p_row04_traceSegment_006_1674_0013, g32p_row04_traceSegment_006_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_006 1701 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_006 1714 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_006_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_006 1701 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1701 13 14, g32p_row04_traceSegment_006_1701_0013, g32p_row04_traceSegment_006_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_006 1674 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1674 27 27, g32p_row04_traceSegment_006_1674_0027, g32p_row04_traceSegment_006_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_006 1620 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1620 54 54, g32p_row04_traceSegment_006_1620_0054, g32p_row04_traceSegment_006_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_006 1512 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1512 108 108, g32p_row04_traceSegment_006_1512_0108, g32p_row04_traceSegment_006_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_006_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_006 1296 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 1296 216 216, g32p_row04_traceSegment_006_1296_0216, g32p_row04_traceSegment_006_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_006 864 864 = [0, 14, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 864 432 432, g32p_row04_traceSegment_006_0864_0432, g32p_row04_traceSegment_006_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_006_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_006 0 1728 = [0, 16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_006 0 864 864, g32p_row04_traceSegment_006_0000_0864, g32p_row04_traceSegment_006_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 6 = [0, 16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_006_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_007 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 7 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_007_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 13 14, g32p_row04_traceSegment_007_0000_0013, g32p_row04_traceSegment_007_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 27 13 14, g32p_row04_traceSegment_007_0027_0013, g32p_row04_traceSegment_007_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 27 27, g32p_row04_traceSegment_007_0000_0027, g32p_row04_traceSegment_007_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 67 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 54 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 54 13 14, g32p_row04_traceSegment_007_0054_0013, g32p_row04_traceSegment_007_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 81 13 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 94 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 81 27 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 81 13 14, g32p_row04_traceSegment_007_0081_0013, g32p_row04_traceSegment_007_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 54 54 = [2, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 54 27 27, g32p_row04_traceSegment_007_0054_0027, g32p_row04_traceSegment_007_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 0 108 = [2, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 54 54, g32p_row04_traceSegment_007_0000_0054, g32p_row04_traceSegment_007_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 108 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 121 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 108 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 108 13 14, g32p_row04_traceSegment_007_0108_0013, g32p_row04_traceSegment_007_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 135 13 14, g32p_row04_traceSegment_007_0135_0013, g32p_row04_traceSegment_007_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 108 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 108 27 27, g32p_row04_traceSegment_007_0108_0027, g32p_row04_traceSegment_007_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 162 13 14, g32p_row04_traceSegment_007_0162_0013, g32p_row04_traceSegment_007_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 189 13 14, g32p_row04_traceSegment_007_0189_0013, g32p_row04_traceSegment_007_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 162 27 27, g32p_row04_traceSegment_007_0162_0027, g32p_row04_traceSegment_007_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 108 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 108 54 54, g32p_row04_traceSegment_007_0108_0054, g32p_row04_traceSegment_007_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 0 216 = [5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 108 108, g32p_row04_traceSegment_007_0000_0108, g32p_row04_traceSegment_007_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 216 13 14, g32p_row04_traceSegment_007_0216_0013, g32p_row04_traceSegment_007_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 243 13 14, g32p_row04_traceSegment_007_0243_0013, g32p_row04_traceSegment_007_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 216 27 27, g32p_row04_traceSegment_007_0216_0027, g32p_row04_traceSegment_007_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 270 13 14, g32p_row04_traceSegment_007_0270_0013, g32p_row04_traceSegment_007_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 297 13 14, g32p_row04_traceSegment_007_0297_0013, g32p_row04_traceSegment_007_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 270 27 27, g32p_row04_traceSegment_007_0270_0027, g32p_row04_traceSegment_007_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 216 54 54, g32p_row04_traceSegment_007_0216_0054, g32p_row04_traceSegment_007_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 324 13 14, g32p_row04_traceSegment_007_0324_0013, g32p_row04_traceSegment_007_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 351 13 14, g32p_row04_traceSegment_007_0351_0013, g32p_row04_traceSegment_007_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 324 27 27, g32p_row04_traceSegment_007_0324_0027, g32p_row04_traceSegment_007_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 378 13 14, g32p_row04_traceSegment_007_0378_0013, g32p_row04_traceSegment_007_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 405 13 14, g32p_row04_traceSegment_007_0405_0013, g32p_row04_traceSegment_007_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 378 27 27, g32p_row04_traceSegment_007_0378_0027, g32p_row04_traceSegment_007_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 324 54 54, g32p_row04_traceSegment_007_0324_0054, g32p_row04_traceSegment_007_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 216 108 108, g32p_row04_traceSegment_007_0216_0108, g32p_row04_traceSegment_007_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_007 0 432 = [5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 216 216, g32p_row04_traceSegment_007_0000_0216, g32p_row04_traceSegment_007_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 432 13 14, g32p_row04_traceSegment_007_0432_0013, g32p_row04_traceSegment_007_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 459 13 14, g32p_row04_traceSegment_007_0459_0013, g32p_row04_traceSegment_007_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 432 27 27, g32p_row04_traceSegment_007_0432_0027, g32p_row04_traceSegment_007_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 499 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 486 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 486 13 14, g32p_row04_traceSegment_007_0486_0013, g32p_row04_traceSegment_007_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 513 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 513 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 513 13 14, g32p_row04_traceSegment_007_0513_0013, g32p_row04_traceSegment_007_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 486 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 486 27 27, g32p_row04_traceSegment_007_0486_0027, g32p_row04_traceSegment_007_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 432 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 432 54 54, g32p_row04_traceSegment_007_0432_0054, g32p_row04_traceSegment_007_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 540 13 14, g32p_row04_traceSegment_007_0540_0013, g32p_row04_traceSegment_007_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 580 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 567 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 567 13 14, g32p_row04_traceSegment_007_0567_0013, g32p_row04_traceSegment_007_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 540 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 540 27 27, g32p_row04_traceSegment_007_0540_0027, g32p_row04_traceSegment_007_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 607 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 594 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 594 13 14, g32p_row04_traceSegment_007_0594_0013, g32p_row04_traceSegment_007_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 621 13 14, g32p_row04_traceSegment_007_0621_0013, g32p_row04_traceSegment_007_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 594 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 594 27 27, g32p_row04_traceSegment_007_0594_0027, g32p_row04_traceSegment_007_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 540 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 540 54 54, g32p_row04_traceSegment_007_0540_0054, g32p_row04_traceSegment_007_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 432 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 432 108 108, g32p_row04_traceSegment_007_0432_0108, g32p_row04_traceSegment_007_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 648 13 14, g32p_row04_traceSegment_007_0648_0013, g32p_row04_traceSegment_007_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 675 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 675 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 675 13 14, g32p_row04_traceSegment_007_0675_0013, g32p_row04_traceSegment_007_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 648 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 648 27 27, g32p_row04_traceSegment_007_0648_0027, g32p_row04_traceSegment_007_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 702 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 702 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 702 13 14, g32p_row04_traceSegment_007_0702_0013, g32p_row04_traceSegment_007_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 729 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 742 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 729 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 729 13 14, g32p_row04_traceSegment_007_0729_0013, g32p_row04_traceSegment_007_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 702 54 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 702 27 27, g32p_row04_traceSegment_007_0702_0027, g32p_row04_traceSegment_007_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 648 108 = [2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 648 54 54, g32p_row04_traceSegment_007_0648_0054, g32p_row04_traceSegment_007_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 756 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 769 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 756 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 756 13 14, g32p_row04_traceSegment_007_0756_0013, g32p_row04_traceSegment_007_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 783 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 796 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 783 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 783 13 14, g32p_row04_traceSegment_007_0783_0013, g32p_row04_traceSegment_007_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 756 54 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 756 27 27, g32p_row04_traceSegment_007_0756_0027, g32p_row04_traceSegment_007_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 810 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 823 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 810 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 810 13 14, g32p_row04_traceSegment_007_0810_0013, g32p_row04_traceSegment_007_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 837 13 14, g32p_row04_traceSegment_007_0837_0013, g32p_row04_traceSegment_007_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 810 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 810 27 27, g32p_row04_traceSegment_007_0810_0027, g32p_row04_traceSegment_007_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 756 108 = [9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 756 54 54, g32p_row04_traceSegment_007_0756_0054, g32p_row04_traceSegment_007_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 648 216 = [11, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 648 108 108, g32p_row04_traceSegment_007_0648_0108, g32p_row04_traceSegment_007_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_007 432 432 = [11, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 432 216 216, g32p_row04_traceSegment_007_0432_0216, g32p_row04_traceSegment_007_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_007 0 864 = [16, 15] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 432 432, g32p_row04_traceSegment_007_0000_0432, g32p_row04_traceSegment_007_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 864 13 14, g32p_row04_traceSegment_007_0864_0013, g32p_row04_traceSegment_007_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 891 13 14, g32p_row04_traceSegment_007_0891_0013, g32p_row04_traceSegment_007_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 864 27 27, g32p_row04_traceSegment_007_0864_0027, g32p_row04_traceSegment_007_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 918 13 14, g32p_row04_traceSegment_007_0918_0013, g32p_row04_traceSegment_007_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 945 13 14, g32p_row04_traceSegment_007_0945_0013, g32p_row04_traceSegment_007_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 918 27 27, g32p_row04_traceSegment_007_0918_0027, g32p_row04_traceSegment_007_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 864 54 54, g32p_row04_traceSegment_007_0864_0054, g32p_row04_traceSegment_007_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 972 13 14, g32p_row04_traceSegment_007_0972_0013, g32p_row04_traceSegment_007_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 999 13 14, g32p_row04_traceSegment_007_0999_0013, g32p_row04_traceSegment_007_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 972 27 27, g32p_row04_traceSegment_007_0972_0027, g32p_row04_traceSegment_007_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1026 13 14, g32p_row04_traceSegment_007_1026_0013, g32p_row04_traceSegment_007_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1053 13 14, g32p_row04_traceSegment_007_1053_0013, g32p_row04_traceSegment_007_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1026 27 27, g32p_row04_traceSegment_007_1026_0027, g32p_row04_traceSegment_007_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 972 54 54, g32p_row04_traceSegment_007_0972_0054, g32p_row04_traceSegment_007_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 864 108 108, g32p_row04_traceSegment_007_0864_0108, g32p_row04_traceSegment_007_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1080 13 14, g32p_row04_traceSegment_007_1080_0013, g32p_row04_traceSegment_007_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1107 13 14, g32p_row04_traceSegment_007_1107_0013, g32p_row04_traceSegment_007_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1080 27 27, g32p_row04_traceSegment_007_1080_0027, g32p_row04_traceSegment_007_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1134 13 14, g32p_row04_traceSegment_007_1134_0013, g32p_row04_traceSegment_007_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1161 13 14, g32p_row04_traceSegment_007_1161_0013, g32p_row04_traceSegment_007_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1134 27 27, g32p_row04_traceSegment_007_1134_0027, g32p_row04_traceSegment_007_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1080 54 54, g32p_row04_traceSegment_007_1080_0054, g32p_row04_traceSegment_007_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1188 13 14, g32p_row04_traceSegment_007_1188_0013, g32p_row04_traceSegment_007_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1215 13 14, g32p_row04_traceSegment_007_1215_0013, g32p_row04_traceSegment_007_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1188 27 27, g32p_row04_traceSegment_007_1188_0027, g32p_row04_traceSegment_007_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1242 13 14, g32p_row04_traceSegment_007_1242_0013, g32p_row04_traceSegment_007_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1269 13 14, g32p_row04_traceSegment_007_1269_0013, g32p_row04_traceSegment_007_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1242 27 27, g32p_row04_traceSegment_007_1242_0027, g32p_row04_traceSegment_007_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1188 54 54, g32p_row04_traceSegment_007_1188_0054, g32p_row04_traceSegment_007_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1080 108 108, g32p_row04_traceSegment_007_1080_0108, g32p_row04_traceSegment_007_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_007 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 864 216 216, g32p_row04_traceSegment_007_0864_0216, g32p_row04_traceSegment_007_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1296 13 14, g32p_row04_traceSegment_007_1296_0013, g32p_row04_traceSegment_007_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1323 13 14, g32p_row04_traceSegment_007_1323_0013, g32p_row04_traceSegment_007_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1296 27 27, g32p_row04_traceSegment_007_1296_0027, g32p_row04_traceSegment_007_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1350 13 14, g32p_row04_traceSegment_007_1350_0013, g32p_row04_traceSegment_007_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1377 13 14, g32p_row04_traceSegment_007_1377_0013, g32p_row04_traceSegment_007_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1350 27 27, g32p_row04_traceSegment_007_1350_0027, g32p_row04_traceSegment_007_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1296 54 54, g32p_row04_traceSegment_007_1296_0054, g32p_row04_traceSegment_007_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1404 13 14, g32p_row04_traceSegment_007_1404_0013, g32p_row04_traceSegment_007_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1431 13 14, g32p_row04_traceSegment_007_1431_0013, g32p_row04_traceSegment_007_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1404 27 27, g32p_row04_traceSegment_007_1404_0027, g32p_row04_traceSegment_007_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1458 13 14, g32p_row04_traceSegment_007_1458_0013, g32p_row04_traceSegment_007_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1485 13 14, g32p_row04_traceSegment_007_1485_0013, g32p_row04_traceSegment_007_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1458 27 27, g32p_row04_traceSegment_007_1458_0027, g32p_row04_traceSegment_007_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1404 54 54, g32p_row04_traceSegment_007_1404_0054, g32p_row04_traceSegment_007_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1296 108 108, g32p_row04_traceSegment_007_1296_0108, g32p_row04_traceSegment_007_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1512 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1512 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1512 13 14, g32p_row04_traceSegment_007_1512_0013, g32p_row04_traceSegment_007_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1552 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1539 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1539 13 14, g32p_row04_traceSegment_007_1539_0013, g32p_row04_traceSegment_007_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1512 54 = [2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1512 27 27, g32p_row04_traceSegment_007_1512_0027, g32p_row04_traceSegment_007_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1566 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1579 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1566 27 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1566 13 14, g32p_row04_traceSegment_007_1566_0013, g32p_row04_traceSegment_007_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1593 13 = [3, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1606 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1593 27 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1593 13 14, g32p_row04_traceSegment_007_1593_0013, g32p_row04_traceSegment_007_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1566 54 = [5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1566 27 27, g32p_row04_traceSegment_007_1566_0027, g32p_row04_traceSegment_007_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 1512 108 = [7, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1512 54 54, g32p_row04_traceSegment_007_1512_0054, g32p_row04_traceSegment_007_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1620 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1620 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1620 13 14, g32p_row04_traceSegment_007_1620_0013, g32p_row04_traceSegment_007_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1647 13 14, g32p_row04_traceSegment_007_1647_0013, g32p_row04_traceSegment_007_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1620 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1620 27 27, g32p_row04_traceSegment_007_1620_0027, g32p_row04_traceSegment_007_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1674 13 14, g32p_row04_traceSegment_007_1674_0013, g32p_row04_traceSegment_007_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_007 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_007 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_007_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_007 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1701 13 14, g32p_row04_traceSegment_007_1701_0013, g32p_row04_traceSegment_007_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_007 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1674 27 27, g32p_row04_traceSegment_007_1674_0027, g32p_row04_traceSegment_007_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_007 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1620 54 54, g32p_row04_traceSegment_007_1620_0054, g32p_row04_traceSegment_007_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_007 1512 216 = [8, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1512 108 108, g32p_row04_traceSegment_007_1512_0108, g32p_row04_traceSegment_007_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_007_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_007 1296 432 = [8, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 1296 216 216, g32p_row04_traceSegment_007_1296_0216, g32p_row04_traceSegment_007_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_007 864 864 = [8, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 864 432 432, g32p_row04_traceSegment_007_0864_0432, g32p_row04_traceSegment_007_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_007_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_007 0 1728 = [24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_007 0 864 864, g32p_row04_traceSegment_007_0000_0864, g32p_row04_traceSegment_007_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 7 = [24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_007_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 0) (g32p_literalTraceValue 3 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_000]
  decide +kernel

theorem g32p_row04_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 1) (g32p_literalTraceValue 3 1)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_001]
  decide +kernel

theorem g32p_row04_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 2) (g32p_literalTraceValue 3 2)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_002]
  decide +kernel

theorem g32p_row04_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 3) (g32p_literalTraceValue 3 3)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_003]
  decide +kernel

theorem g32p_row04_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 4) (g32p_literalTraceValue 3 4)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_004]
  decide +kernel

theorem g32p_row04_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 5) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 5) (g32p_literalTraceValue 3 5)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_005]
  decide +kernel

theorem g32p_row04_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 6) (g32p_literalTraceValue 3 6)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row04_traceCoefficients_006]
  decide +kernel

theorem g32p_row04_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 7) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 7) (g32p_literalTraceValue 3 7)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_007]
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

private def g32p_row04_traceSegment_008 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 8 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_008_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 13 14, g32p_row04_traceSegment_008_0000_0013, g32p_row04_traceSegment_008_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 27 13 14, g32p_row04_traceSegment_008_0027_0013, g32p_row04_traceSegment_008_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 27 27, g32p_row04_traceSegment_008_0000_0027, g32p_row04_traceSegment_008_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 54 13 14, g32p_row04_traceSegment_008_0054_0013, g32p_row04_traceSegment_008_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 81 13 14, g32p_row04_traceSegment_008_0081_0013, g32p_row04_traceSegment_008_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 54 27 27, g32p_row04_traceSegment_008_0054_0027, g32p_row04_traceSegment_008_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 54 54, g32p_row04_traceSegment_008_0000_0054, g32p_row04_traceSegment_008_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 108 13 14, g32p_row04_traceSegment_008_0108_0013, g32p_row04_traceSegment_008_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 135 13 14, g32p_row04_traceSegment_008_0135_0013, g32p_row04_traceSegment_008_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 108 27 27, g32p_row04_traceSegment_008_0108_0027, g32p_row04_traceSegment_008_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 162 13 14, g32p_row04_traceSegment_008_0162_0013, g32p_row04_traceSegment_008_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 189 13 14, g32p_row04_traceSegment_008_0189_0013, g32p_row04_traceSegment_008_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 162 27 27, g32p_row04_traceSegment_008_0162_0027, g32p_row04_traceSegment_008_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 108 54 54, g32p_row04_traceSegment_008_0108_0054, g32p_row04_traceSegment_008_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 108 108, g32p_row04_traceSegment_008_0000_0108, g32p_row04_traceSegment_008_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 216 13 14, g32p_row04_traceSegment_008_0216_0013, g32p_row04_traceSegment_008_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 243 13 14, g32p_row04_traceSegment_008_0243_0013, g32p_row04_traceSegment_008_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 216 27 27, g32p_row04_traceSegment_008_0216_0027, g32p_row04_traceSegment_008_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 270 13 14, g32p_row04_traceSegment_008_0270_0013, g32p_row04_traceSegment_008_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 297 13 14, g32p_row04_traceSegment_008_0297_0013, g32p_row04_traceSegment_008_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 270 27 27, g32p_row04_traceSegment_008_0270_0027, g32p_row04_traceSegment_008_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 216 54 54, g32p_row04_traceSegment_008_0216_0054, g32p_row04_traceSegment_008_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 324 13 14, g32p_row04_traceSegment_008_0324_0013, g32p_row04_traceSegment_008_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 351 13 14, g32p_row04_traceSegment_008_0351_0013, g32p_row04_traceSegment_008_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 324 27 27, g32p_row04_traceSegment_008_0324_0027, g32p_row04_traceSegment_008_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 378 13 14, g32p_row04_traceSegment_008_0378_0013, g32p_row04_traceSegment_008_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 405 13 14, g32p_row04_traceSegment_008_0405_0013, g32p_row04_traceSegment_008_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 378 27 27, g32p_row04_traceSegment_008_0378_0027, g32p_row04_traceSegment_008_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 324 54 54, g32p_row04_traceSegment_008_0324_0054, g32p_row04_traceSegment_008_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 216 108 108, g32p_row04_traceSegment_008_0216_0108, g32p_row04_traceSegment_008_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_008 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 216 216, g32p_row04_traceSegment_008_0000_0216, g32p_row04_traceSegment_008_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 432 13 14, g32p_row04_traceSegment_008_0432_0013, g32p_row04_traceSegment_008_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 459 13 14, g32p_row04_traceSegment_008_0459_0013, g32p_row04_traceSegment_008_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 432 27 27, g32p_row04_traceSegment_008_0432_0027, g32p_row04_traceSegment_008_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 486 13 14, g32p_row04_traceSegment_008_0486_0013, g32p_row04_traceSegment_008_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 513 13 14, g32p_row04_traceSegment_008_0513_0013, g32p_row04_traceSegment_008_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 486 27 27, g32p_row04_traceSegment_008_0486_0027, g32p_row04_traceSegment_008_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 432 54 54, g32p_row04_traceSegment_008_0432_0054, g32p_row04_traceSegment_008_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 540 13 14, g32p_row04_traceSegment_008_0540_0013, g32p_row04_traceSegment_008_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 567 13 14, g32p_row04_traceSegment_008_0567_0013, g32p_row04_traceSegment_008_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 540 27 27, g32p_row04_traceSegment_008_0540_0027, g32p_row04_traceSegment_008_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 594 13 14, g32p_row04_traceSegment_008_0594_0013, g32p_row04_traceSegment_008_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 621 13 14, g32p_row04_traceSegment_008_0621_0013, g32p_row04_traceSegment_008_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 594 27 27, g32p_row04_traceSegment_008_0594_0027, g32p_row04_traceSegment_008_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 540 54 54, g32p_row04_traceSegment_008_0540_0054, g32p_row04_traceSegment_008_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 432 108 108, g32p_row04_traceSegment_008_0432_0108, g32p_row04_traceSegment_008_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 648 13 14, g32p_row04_traceSegment_008_0648_0013, g32p_row04_traceSegment_008_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 675 13 14, g32p_row04_traceSegment_008_0675_0013, g32p_row04_traceSegment_008_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 648 27 27, g32p_row04_traceSegment_008_0648_0027, g32p_row04_traceSegment_008_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 702 13 14, g32p_row04_traceSegment_008_0702_0013, g32p_row04_traceSegment_008_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 729 13 14, g32p_row04_traceSegment_008_0729_0013, g32p_row04_traceSegment_008_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 702 27 27, g32p_row04_traceSegment_008_0702_0027, g32p_row04_traceSegment_008_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 648 54 54, g32p_row04_traceSegment_008_0648_0054, g32p_row04_traceSegment_008_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 756 13 14, g32p_row04_traceSegment_008_0756_0013, g32p_row04_traceSegment_008_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 783 13 14, g32p_row04_traceSegment_008_0783_0013, g32p_row04_traceSegment_008_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 756 27 27, g32p_row04_traceSegment_008_0756_0027, g32p_row04_traceSegment_008_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 810 13 14, g32p_row04_traceSegment_008_0810_0013, g32p_row04_traceSegment_008_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 837 13 14, g32p_row04_traceSegment_008_0837_0013, g32p_row04_traceSegment_008_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 810 27 27, g32p_row04_traceSegment_008_0810_0027, g32p_row04_traceSegment_008_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 756 54 54, g32p_row04_traceSegment_008_0756_0054, g32p_row04_traceSegment_008_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 648 108 108, g32p_row04_traceSegment_008_0648_0108, g32p_row04_traceSegment_008_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_008 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 432 216 216, g32p_row04_traceSegment_008_0432_0216, g32p_row04_traceSegment_008_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_008 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 432 432, g32p_row04_traceSegment_008_0000_0432, g32p_row04_traceSegment_008_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 864 13 14, g32p_row04_traceSegment_008_0864_0013, g32p_row04_traceSegment_008_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 891 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 904 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 891 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 891 13 14, g32p_row04_traceSegment_008_0891_0013, g32p_row04_traceSegment_008_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 864 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 864 27 27, g32p_row04_traceSegment_008_0864_0027, g32p_row04_traceSegment_008_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 918 13 14, g32p_row04_traceSegment_008_0918_0013, g32p_row04_traceSegment_008_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 945 13 14, g32p_row04_traceSegment_008_0945_0013, g32p_row04_traceSegment_008_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 918 27 27, g32p_row04_traceSegment_008_0918_0027, g32p_row04_traceSegment_008_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 864 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 864 54 54, g32p_row04_traceSegment_008_0864_0054, g32p_row04_traceSegment_008_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 972 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 972 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 972 13 14, g32p_row04_traceSegment_008_0972_0013, g32p_row04_traceSegment_008_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 999 13 14, g32p_row04_traceSegment_008_0999_0013, g32p_row04_traceSegment_008_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 972 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 972 27 27, g32p_row04_traceSegment_008_0972_0027, g32p_row04_traceSegment_008_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1026 13 14, g32p_row04_traceSegment_008_1026_0013, g32p_row04_traceSegment_008_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1066 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1053 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1053 13 14, g32p_row04_traceSegment_008_1053_0013, g32p_row04_traceSegment_008_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1026 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1026 27 27, g32p_row04_traceSegment_008_1026_0027, g32p_row04_traceSegment_008_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 972 108 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 972 54 54, g32p_row04_traceSegment_008_0972_0054, g32p_row04_traceSegment_008_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 864 216 = [4, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 864 108 108, g32p_row04_traceSegment_008_0864_0108, g32p_row04_traceSegment_008_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1093 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1080 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1080 13 14, g32p_row04_traceSegment_008_1080_0013, g32p_row04_traceSegment_008_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1107 13 14, g32p_row04_traceSegment_008_1107_0013, g32p_row04_traceSegment_008_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1080 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1080 27 27, g32p_row04_traceSegment_008_1080_0027, g32p_row04_traceSegment_008_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1134 13 14, g32p_row04_traceSegment_008_1134_0013, g32p_row04_traceSegment_008_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1161 13 14, g32p_row04_traceSegment_008_1161_0013, g32p_row04_traceSegment_008_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1134 27 27, g32p_row04_traceSegment_008_1134_0027, g32p_row04_traceSegment_008_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 1080 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1080 54 54, g32p_row04_traceSegment_008_1080_0054, g32p_row04_traceSegment_008_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1188 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1188 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1188 13 14, g32p_row04_traceSegment_008_1188_0013, g32p_row04_traceSegment_008_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1215 13 14, g32p_row04_traceSegment_008_1215_0013, g32p_row04_traceSegment_008_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1188 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1188 27 27, g32p_row04_traceSegment_008_1188_0027, g32p_row04_traceSegment_008_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1242 13 14, g32p_row04_traceSegment_008_1242_0013, g32p_row04_traceSegment_008_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1269 13 14, g32p_row04_traceSegment_008_1269_0013, g32p_row04_traceSegment_008_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1242 27 27, g32p_row04_traceSegment_008_1242_0027, g32p_row04_traceSegment_008_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 1188 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1188 54 54, g32p_row04_traceSegment_008_1188_0054, g32p_row04_traceSegment_008_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 1080 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1080 108 108, g32p_row04_traceSegment_008_1080_0108, g32p_row04_traceSegment_008_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_008 864 432 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 864 216 216, g32p_row04_traceSegment_008_0864_0216, g32p_row04_traceSegment_008_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1296 13 14, g32p_row04_traceSegment_008_1296_0013, g32p_row04_traceSegment_008_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1323 13 14, g32p_row04_traceSegment_008_1323_0013, g32p_row04_traceSegment_008_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1296 27 27, g32p_row04_traceSegment_008_1296_0027, g32p_row04_traceSegment_008_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1350 13 14, g32p_row04_traceSegment_008_1350_0013, g32p_row04_traceSegment_008_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1377 13 14, g32p_row04_traceSegment_008_1377_0013, g32p_row04_traceSegment_008_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1350 27 27, g32p_row04_traceSegment_008_1350_0027, g32p_row04_traceSegment_008_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1296 54 54, g32p_row04_traceSegment_008_1296_0054, g32p_row04_traceSegment_008_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1404 13 14, g32p_row04_traceSegment_008_1404_0013, g32p_row04_traceSegment_008_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1431 13 14, g32p_row04_traceSegment_008_1431_0013, g32p_row04_traceSegment_008_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1404 27 27, g32p_row04_traceSegment_008_1404_0027, g32p_row04_traceSegment_008_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1458 13 14, g32p_row04_traceSegment_008_1458_0013, g32p_row04_traceSegment_008_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1485 13 14, g32p_row04_traceSegment_008_1485_0013, g32p_row04_traceSegment_008_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1458 27 27, g32p_row04_traceSegment_008_1458_0027, g32p_row04_traceSegment_008_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1404 54 54, g32p_row04_traceSegment_008_1404_0054, g32p_row04_traceSegment_008_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1296 108 108, g32p_row04_traceSegment_008_1296_0108, g32p_row04_traceSegment_008_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1512 13 14, g32p_row04_traceSegment_008_1512_0013, g32p_row04_traceSegment_008_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1539 13 14, g32p_row04_traceSegment_008_1539_0013, g32p_row04_traceSegment_008_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1512 27 27, g32p_row04_traceSegment_008_1512_0027, g32p_row04_traceSegment_008_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1566 13 14, g32p_row04_traceSegment_008_1566_0013, g32p_row04_traceSegment_008_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1593 13 14, g32p_row04_traceSegment_008_1593_0013, g32p_row04_traceSegment_008_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1566 27 27, g32p_row04_traceSegment_008_1566_0027, g32p_row04_traceSegment_008_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1512 54 54, g32p_row04_traceSegment_008_1512_0054, g32p_row04_traceSegment_008_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1620 13 14, g32p_row04_traceSegment_008_1620_0013, g32p_row04_traceSegment_008_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1647 13 14, g32p_row04_traceSegment_008_1647_0013, g32p_row04_traceSegment_008_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1620 27 27, g32p_row04_traceSegment_008_1620_0027, g32p_row04_traceSegment_008_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1674 13 14, g32p_row04_traceSegment_008_1674_0013, g32p_row04_traceSegment_008_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_008 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_008 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_008_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_008 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1701 13 14, g32p_row04_traceSegment_008_1701_0013, g32p_row04_traceSegment_008_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_008 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1674 27 27, g32p_row04_traceSegment_008_1674_0027, g32p_row04_traceSegment_008_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_008 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1620 54 54, g32p_row04_traceSegment_008_1620_0054, g32p_row04_traceSegment_008_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_008 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1512 108 108, g32p_row04_traceSegment_008_1512_0108, g32p_row04_traceSegment_008_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_008_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_008 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 1296 216 216, g32p_row04_traceSegment_008_1296_0216, g32p_row04_traceSegment_008_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_008 864 864 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 864 432 432, g32p_row04_traceSegment_008_0864_0432, g32p_row04_traceSegment_008_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_008_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_008 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_008 0 864 864, g32p_row04_traceSegment_008_0000_0864, g32p_row04_traceSegment_008_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 8 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_008_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_010 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 10 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_010_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 13 14, g32p_row04_traceSegment_010_0000_0013, g32p_row04_traceSegment_010_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 27 13 14, g32p_row04_traceSegment_010_0027_0013, g32p_row04_traceSegment_010_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 27 27, g32p_row04_traceSegment_010_0000_0027, g32p_row04_traceSegment_010_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 67 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 54 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 54 13 14, g32p_row04_traceSegment_010_0054_0013, g32p_row04_traceSegment_010_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 81 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 94 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 81 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 81 13 14, g32p_row04_traceSegment_010_0081_0013, g32p_row04_traceSegment_010_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 54 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 54 27 27, g32p_row04_traceSegment_010_0054_0027, g32p_row04_traceSegment_010_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 0 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 54 54, g32p_row04_traceSegment_010_0000_0054, g32p_row04_traceSegment_010_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 108 13 14, g32p_row04_traceSegment_010_0108_0013, g32p_row04_traceSegment_010_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 135 13 14, g32p_row04_traceSegment_010_0135_0013, g32p_row04_traceSegment_010_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 108 27 27, g32p_row04_traceSegment_010_0108_0027, g32p_row04_traceSegment_010_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 162 13 14, g32p_row04_traceSegment_010_0162_0013, g32p_row04_traceSegment_010_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 189 13 14, g32p_row04_traceSegment_010_0189_0013, g32p_row04_traceSegment_010_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 162 27 27, g32p_row04_traceSegment_010_0162_0027, g32p_row04_traceSegment_010_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 108 54 54, g32p_row04_traceSegment_010_0108_0054, g32p_row04_traceSegment_010_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 0 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 108 108, g32p_row04_traceSegment_010_0000_0108, g32p_row04_traceSegment_010_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 216 13 14, g32p_row04_traceSegment_010_0216_0013, g32p_row04_traceSegment_010_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 243 13 14, g32p_row04_traceSegment_010_0243_0013, g32p_row04_traceSegment_010_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 216 27 27, g32p_row04_traceSegment_010_0216_0027, g32p_row04_traceSegment_010_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 270 13 14, g32p_row04_traceSegment_010_0270_0013, g32p_row04_traceSegment_010_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 297 13 14, g32p_row04_traceSegment_010_0297_0013, g32p_row04_traceSegment_010_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 270 27 27, g32p_row04_traceSegment_010_0270_0027, g32p_row04_traceSegment_010_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 216 54 54, g32p_row04_traceSegment_010_0216_0054, g32p_row04_traceSegment_010_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 324 13 14, g32p_row04_traceSegment_010_0324_0013, g32p_row04_traceSegment_010_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 351 13 14, g32p_row04_traceSegment_010_0351_0013, g32p_row04_traceSegment_010_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 324 27 27, g32p_row04_traceSegment_010_0324_0027, g32p_row04_traceSegment_010_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 378 13 14, g32p_row04_traceSegment_010_0378_0013, g32p_row04_traceSegment_010_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 405 13 14, g32p_row04_traceSegment_010_0405_0013, g32p_row04_traceSegment_010_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 378 27 27, g32p_row04_traceSegment_010_0378_0027, g32p_row04_traceSegment_010_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 324 54 54, g32p_row04_traceSegment_010_0324_0054, g32p_row04_traceSegment_010_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 216 108 108, g32p_row04_traceSegment_010_0216_0108, g32p_row04_traceSegment_010_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_010 0 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 216 216, g32p_row04_traceSegment_010_0000_0216, g32p_row04_traceSegment_010_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 432 13 14, g32p_row04_traceSegment_010_0432_0013, g32p_row04_traceSegment_010_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 459 13 14, g32p_row04_traceSegment_010_0459_0013, g32p_row04_traceSegment_010_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 432 27 27, g32p_row04_traceSegment_010_0432_0027, g32p_row04_traceSegment_010_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 499 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 486 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 486 13 14, g32p_row04_traceSegment_010_0486_0013, g32p_row04_traceSegment_010_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 526 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 513 13 14, g32p_row04_traceSegment_010_0513_0013, g32p_row04_traceSegment_010_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 486 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 486 27 27, g32p_row04_traceSegment_010_0486_0027, g32p_row04_traceSegment_010_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 432 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 432 54 54, g32p_row04_traceSegment_010_0432_0054, g32p_row04_traceSegment_010_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 540 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 553 14 = [2, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 540 27 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 540 13 14, g32p_row04_traceSegment_010_0540_0013, g32p_row04_traceSegment_010_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 567 13 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 580 14 = [1, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 567 27 = [2, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 567 13 14, g32p_row04_traceSegment_010_0567_0013, g32p_row04_traceSegment_010_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 540 54 = [5, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 540 27 27, g32p_row04_traceSegment_010_0540_0027, g32p_row04_traceSegment_010_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 594 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 607 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 594 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 594 13 14, g32p_row04_traceSegment_010_0594_0013, g32p_row04_traceSegment_010_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 621 13 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 634 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 621 27 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 621 13 14, g32p_row04_traceSegment_010_0621_0013, g32p_row04_traceSegment_010_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 594 54 = [3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 594 27 27, g32p_row04_traceSegment_010_0594_0027, g32p_row04_traceSegment_010_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 540 108 = [8, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 540 54 54, g32p_row04_traceSegment_010_0540_0054, g32p_row04_traceSegment_010_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 432 216 = [11, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 432 108 108, g32p_row04_traceSegment_010_0432_0108, g32p_row04_traceSegment_010_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 648 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 661 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 648 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 648 13 14, g32p_row04_traceSegment_010_0648_0013, g32p_row04_traceSegment_010_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 675 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 675 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 675 13 14, g32p_row04_traceSegment_010_0675_0013, g32p_row04_traceSegment_010_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 648 54 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 648 27 27, g32p_row04_traceSegment_010_0648_0027, g32p_row04_traceSegment_010_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 702 13 14, g32p_row04_traceSegment_010_0702_0013, g32p_row04_traceSegment_010_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 729 13 14, g32p_row04_traceSegment_010_0729_0013, g32p_row04_traceSegment_010_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 702 27 27, g32p_row04_traceSegment_010_0702_0027, g32p_row04_traceSegment_010_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 648 108 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 648 54 54, g32p_row04_traceSegment_010_0648_0054, g32p_row04_traceSegment_010_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 756 13 14, g32p_row04_traceSegment_010_0756_0013, g32p_row04_traceSegment_010_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 783 13 14, g32p_row04_traceSegment_010_0783_0013, g32p_row04_traceSegment_010_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 756 27 27, g32p_row04_traceSegment_010_0756_0027, g32p_row04_traceSegment_010_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 810 13 14, g32p_row04_traceSegment_010_0810_0013, g32p_row04_traceSegment_010_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 837 13 14, g32p_row04_traceSegment_010_0837_0013, g32p_row04_traceSegment_010_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 810 27 27, g32p_row04_traceSegment_010_0810_0027, g32p_row04_traceSegment_010_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 756 54 54, g32p_row04_traceSegment_010_0756_0054, g32p_row04_traceSegment_010_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 648 216 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 648 108 108, g32p_row04_traceSegment_010_0648_0108, g32p_row04_traceSegment_010_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_010 432 432 = [12, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 432 216 216, g32p_row04_traceSegment_010_0432_0216, g32p_row04_traceSegment_010_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_010 0 864 = [12, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 432 432, g32p_row04_traceSegment_010_0000_0432, g32p_row04_traceSegment_010_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 864 13 14, g32p_row04_traceSegment_010_0864_0013, g32p_row04_traceSegment_010_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 891 13 14, g32p_row04_traceSegment_010_0891_0013, g32p_row04_traceSegment_010_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 864 27 27, g32p_row04_traceSegment_010_0864_0027, g32p_row04_traceSegment_010_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 918 13 14, g32p_row04_traceSegment_010_0918_0013, g32p_row04_traceSegment_010_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 945 13 14, g32p_row04_traceSegment_010_0945_0013, g32p_row04_traceSegment_010_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 918 27 27, g32p_row04_traceSegment_010_0918_0027, g32p_row04_traceSegment_010_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 864 54 54, g32p_row04_traceSegment_010_0864_0054, g32p_row04_traceSegment_010_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 972 13 14, g32p_row04_traceSegment_010_0972_0013, g32p_row04_traceSegment_010_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 999 13 14, g32p_row04_traceSegment_010_0999_0013, g32p_row04_traceSegment_010_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 972 27 27, g32p_row04_traceSegment_010_0972_0027, g32p_row04_traceSegment_010_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1026 13 14, g32p_row04_traceSegment_010_1026_0013, g32p_row04_traceSegment_010_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1053 13 14, g32p_row04_traceSegment_010_1053_0013, g32p_row04_traceSegment_010_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1026 27 27, g32p_row04_traceSegment_010_1026_0027, g32p_row04_traceSegment_010_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 972 54 54, g32p_row04_traceSegment_010_0972_0054, g32p_row04_traceSegment_010_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 864 108 108, g32p_row04_traceSegment_010_0864_0108, g32p_row04_traceSegment_010_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1080 13 14, g32p_row04_traceSegment_010_1080_0013, g32p_row04_traceSegment_010_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1107 13 14, g32p_row04_traceSegment_010_1107_0013, g32p_row04_traceSegment_010_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1080 27 27, g32p_row04_traceSegment_010_1080_0027, g32p_row04_traceSegment_010_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1134 13 14, g32p_row04_traceSegment_010_1134_0013, g32p_row04_traceSegment_010_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1161 13 14, g32p_row04_traceSegment_010_1161_0013, g32p_row04_traceSegment_010_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1134 27 27, g32p_row04_traceSegment_010_1134_0027, g32p_row04_traceSegment_010_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1080 54 54, g32p_row04_traceSegment_010_1080_0054, g32p_row04_traceSegment_010_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1188 13 14, g32p_row04_traceSegment_010_1188_0013, g32p_row04_traceSegment_010_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1215 13 14, g32p_row04_traceSegment_010_1215_0013, g32p_row04_traceSegment_010_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1188 27 27, g32p_row04_traceSegment_010_1188_0027, g32p_row04_traceSegment_010_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1242 13 14, g32p_row04_traceSegment_010_1242_0013, g32p_row04_traceSegment_010_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1269 13 14, g32p_row04_traceSegment_010_1269_0013, g32p_row04_traceSegment_010_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1242 27 27, g32p_row04_traceSegment_010_1242_0027, g32p_row04_traceSegment_010_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1188 54 54, g32p_row04_traceSegment_010_1188_0054, g32p_row04_traceSegment_010_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1080 108 108, g32p_row04_traceSegment_010_1080_0108, g32p_row04_traceSegment_010_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_010 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 864 216 216, g32p_row04_traceSegment_010_0864_0216, g32p_row04_traceSegment_010_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1296 13 14, g32p_row04_traceSegment_010_1296_0013, g32p_row04_traceSegment_010_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1323 13 14, g32p_row04_traceSegment_010_1323_0013, g32p_row04_traceSegment_010_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1296 27 27, g32p_row04_traceSegment_010_1296_0027, g32p_row04_traceSegment_010_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1350 13 14, g32p_row04_traceSegment_010_1350_0013, g32p_row04_traceSegment_010_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1377 13 14, g32p_row04_traceSegment_010_1377_0013, g32p_row04_traceSegment_010_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1350 27 27, g32p_row04_traceSegment_010_1350_0027, g32p_row04_traceSegment_010_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1296 54 54, g32p_row04_traceSegment_010_1296_0054, g32p_row04_traceSegment_010_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1404 13 14, g32p_row04_traceSegment_010_1404_0013, g32p_row04_traceSegment_010_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1431 13 14, g32p_row04_traceSegment_010_1431_0013, g32p_row04_traceSegment_010_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1404 27 27, g32p_row04_traceSegment_010_1404_0027, g32p_row04_traceSegment_010_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1458 13 14, g32p_row04_traceSegment_010_1458_0013, g32p_row04_traceSegment_010_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1485 13 14, g32p_row04_traceSegment_010_1485_0013, g32p_row04_traceSegment_010_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1458 27 27, g32p_row04_traceSegment_010_1458_0027, g32p_row04_traceSegment_010_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1404 54 54, g32p_row04_traceSegment_010_1404_0054, g32p_row04_traceSegment_010_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1296 108 108, g32p_row04_traceSegment_010_1296_0108, g32p_row04_traceSegment_010_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1525 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1512 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1512 13 14, g32p_row04_traceSegment_010_1512_0013, g32p_row04_traceSegment_010_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1539 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1539 13 14, g32p_row04_traceSegment_010_1539_0013, g32p_row04_traceSegment_010_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1512 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1512 27 27, g32p_row04_traceSegment_010_1512_0027, g32p_row04_traceSegment_010_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1566 13 14, g32p_row04_traceSegment_010_1566_0013, g32p_row04_traceSegment_010_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1593 13 14, g32p_row04_traceSegment_010_1593_0013, g32p_row04_traceSegment_010_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1566 27 27, g32p_row04_traceSegment_010_1566_0027, g32p_row04_traceSegment_010_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 1512 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1512 54 54, g32p_row04_traceSegment_010_1512_0054, g32p_row04_traceSegment_010_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1633 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1620 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1620 13 14, g32p_row04_traceSegment_010_1620_0013, g32p_row04_traceSegment_010_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1647 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1660 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1647 27 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1647 13 14, g32p_row04_traceSegment_010_1647_0013, g32p_row04_traceSegment_010_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1620 54 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1620 27 27, g32p_row04_traceSegment_010_1620_0027, g32p_row04_traceSegment_010_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1674 13 14, g32p_row04_traceSegment_010_1674_0013, g32p_row04_traceSegment_010_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_010 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_010 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_010_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_010 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1701 13 14, g32p_row04_traceSegment_010_1701_0013, g32p_row04_traceSegment_010_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_010 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1674 27 27, g32p_row04_traceSegment_010_1674_0027, g32p_row04_traceSegment_010_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_010 1620 108 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1620 54 54, g32p_row04_traceSegment_010_1620_0054, g32p_row04_traceSegment_010_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_010 1512 216 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1512 108 108, g32p_row04_traceSegment_010_1512_0108, g32p_row04_traceSegment_010_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_010_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_010 1296 432 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 1296 216 216, g32p_row04_traceSegment_010_1296_0216, g32p_row04_traceSegment_010_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_010 864 864 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 864 432 432, g32p_row04_traceSegment_010_0864_0432, g32p_row04_traceSegment_010_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_010_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_010 0 1728 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_010 0 864 864, g32p_row04_traceSegment_010_0000_0864, g32p_row04_traceSegment_010_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 10 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_010_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_011 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 11 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_011_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 0 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 0 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 13 14, g32p_row04_traceSegment_011_0000_0013, g32p_row04_traceSegment_011_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 27 13 14, g32p_row04_traceSegment_011_0027_0013, g32p_row04_traceSegment_011_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 27 27, g32p_row04_traceSegment_011_0000_0027, g32p_row04_traceSegment_011_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 54 13 14, g32p_row04_traceSegment_011_0054_0013, g32p_row04_traceSegment_011_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 81 13 14, g32p_row04_traceSegment_011_0081_0013, g32p_row04_traceSegment_011_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 54 27 27, g32p_row04_traceSegment_011_0054_0027, g32p_row04_traceSegment_011_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 54 54, g32p_row04_traceSegment_011_0000_0054, g32p_row04_traceSegment_011_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 108 13 14, g32p_row04_traceSegment_011_0108_0013, g32p_row04_traceSegment_011_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 135 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 135 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 135 13 14, g32p_row04_traceSegment_011_0135_0013, g32p_row04_traceSegment_011_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 108 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 108 27 27, g32p_row04_traceSegment_011_0108_0027, g32p_row04_traceSegment_011_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 162 13 14, g32p_row04_traceSegment_011_0162_0013, g32p_row04_traceSegment_011_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 189 13 14, g32p_row04_traceSegment_011_0189_0013, g32p_row04_traceSegment_011_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 162 27 27, g32p_row04_traceSegment_011_0162_0027, g32p_row04_traceSegment_011_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 108 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 108 54 54, g32p_row04_traceSegment_011_0108_0054, g32p_row04_traceSegment_011_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 0 216 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 108 108, g32p_row04_traceSegment_011_0000_0108, g32p_row04_traceSegment_011_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 216 13 14, g32p_row04_traceSegment_011_0216_0013, g32p_row04_traceSegment_011_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 243 13 14, g32p_row04_traceSegment_011_0243_0013, g32p_row04_traceSegment_011_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 216 27 27, g32p_row04_traceSegment_011_0216_0027, g32p_row04_traceSegment_011_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 270 13 14, g32p_row04_traceSegment_011_0270_0013, g32p_row04_traceSegment_011_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 297 13 14, g32p_row04_traceSegment_011_0297_0013, g32p_row04_traceSegment_011_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 270 27 27, g32p_row04_traceSegment_011_0270_0027, g32p_row04_traceSegment_011_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 216 54 54, g32p_row04_traceSegment_011_0216_0054, g32p_row04_traceSegment_011_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 337 14 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 324 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 324 13 14, g32p_row04_traceSegment_011_0324_0013, g32p_row04_traceSegment_011_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 351 13 14, g32p_row04_traceSegment_011_0351_0013, g32p_row04_traceSegment_011_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 324 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 324 27 27, g32p_row04_traceSegment_011_0324_0027, g32p_row04_traceSegment_011_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 378 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 391 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 378 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 378 13 14, g32p_row04_traceSegment_011_0378_0013, g32p_row04_traceSegment_011_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 418 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 405 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 405 13 14, g32p_row04_traceSegment_011_0405_0013, g32p_row04_traceSegment_011_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 378 54 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 378 27 27, g32p_row04_traceSegment_011_0378_0027, g32p_row04_traceSegment_011_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 324 108 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 324 54 54, g32p_row04_traceSegment_011_0324_0054, g32p_row04_traceSegment_011_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 216 216 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 216 108 108, g32p_row04_traceSegment_011_0216_0108, g32p_row04_traceSegment_011_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_011 0 432 = [12, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 216 216, g32p_row04_traceSegment_011_0000_0216, g32p_row04_traceSegment_011_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 432 13 14, g32p_row04_traceSegment_011_0432_0013, g32p_row04_traceSegment_011_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 459 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 472 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 459 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 459 13 14, g32p_row04_traceSegment_011_0459_0013, g32p_row04_traceSegment_011_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 432 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 432 27 27, g32p_row04_traceSegment_011_0432_0027, g32p_row04_traceSegment_011_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 486 13 14, g32p_row04_traceSegment_011_0486_0013, g32p_row04_traceSegment_011_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 513 13 14, g32p_row04_traceSegment_011_0513_0013, g32p_row04_traceSegment_011_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 486 27 27, g32p_row04_traceSegment_011_0486_0027, g32p_row04_traceSegment_011_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 432 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 432 54 54, g32p_row04_traceSegment_011_0432_0054, g32p_row04_traceSegment_011_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 540 13 14, g32p_row04_traceSegment_011_0540_0013, g32p_row04_traceSegment_011_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 567 13 14, g32p_row04_traceSegment_011_0567_0013, g32p_row04_traceSegment_011_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 540 27 27, g32p_row04_traceSegment_011_0540_0027, g32p_row04_traceSegment_011_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 594 13 14, g32p_row04_traceSegment_011_0594_0013, g32p_row04_traceSegment_011_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 621 13 14, g32p_row04_traceSegment_011_0621_0013, g32p_row04_traceSegment_011_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 594 27 27, g32p_row04_traceSegment_011_0594_0027, g32p_row04_traceSegment_011_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 540 54 54, g32p_row04_traceSegment_011_0540_0054, g32p_row04_traceSegment_011_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 432 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 432 108 108, g32p_row04_traceSegment_011_0432_0108, g32p_row04_traceSegment_011_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 648 13 14, g32p_row04_traceSegment_011_0648_0013, g32p_row04_traceSegment_011_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 675 13 14, g32p_row04_traceSegment_011_0675_0013, g32p_row04_traceSegment_011_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 648 27 27, g32p_row04_traceSegment_011_0648_0027, g32p_row04_traceSegment_011_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 702 13 14, g32p_row04_traceSegment_011_0702_0013, g32p_row04_traceSegment_011_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 729 13 14, g32p_row04_traceSegment_011_0729_0013, g32p_row04_traceSegment_011_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 702 27 27, g32p_row04_traceSegment_011_0702_0027, g32p_row04_traceSegment_011_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 648 54 54, g32p_row04_traceSegment_011_0648_0054, g32p_row04_traceSegment_011_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 756 13 14, g32p_row04_traceSegment_011_0756_0013, g32p_row04_traceSegment_011_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 783 13 14, g32p_row04_traceSegment_011_0783_0013, g32p_row04_traceSegment_011_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 756 27 27, g32p_row04_traceSegment_011_0756_0027, g32p_row04_traceSegment_011_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 823 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 810 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 810 13 14, g32p_row04_traceSegment_011_0810_0013, g32p_row04_traceSegment_011_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 837 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 837 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 837 13 14, g32p_row04_traceSegment_011_0837_0013, g32p_row04_traceSegment_011_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 810 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 810 27 27, g32p_row04_traceSegment_011_0810_0027, g32p_row04_traceSegment_011_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 756 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 756 54 54, g32p_row04_traceSegment_011_0756_0054, g32p_row04_traceSegment_011_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 648 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 648 108 108, g32p_row04_traceSegment_011_0648_0108, g32p_row04_traceSegment_011_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_011 432 432 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 432 216 216, g32p_row04_traceSegment_011_0432_0216, g32p_row04_traceSegment_011_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_011 0 864 = [14, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 432 432, g32p_row04_traceSegment_011_0000_0432, g32p_row04_traceSegment_011_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 864 13 14, g32p_row04_traceSegment_011_0864_0013, g32p_row04_traceSegment_011_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 891 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 904 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 891 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 891 13 14, g32p_row04_traceSegment_011_0891_0013, g32p_row04_traceSegment_011_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 864 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 864 27 27, g32p_row04_traceSegment_011_0864_0027, g32p_row04_traceSegment_011_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 931 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 918 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 918 13 14, g32p_row04_traceSegment_011_0918_0013, g32p_row04_traceSegment_011_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 958 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 945 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 945 13 14, g32p_row04_traceSegment_011_0945_0013, g32p_row04_traceSegment_011_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 918 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 918 27 27, g32p_row04_traceSegment_011_0918_0027, g32p_row04_traceSegment_011_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 864 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 864 54 54, g32p_row04_traceSegment_011_0864_0054, g32p_row04_traceSegment_011_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 972 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 985 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 972 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 972 13 14, g32p_row04_traceSegment_011_0972_0013, g32p_row04_traceSegment_011_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1012 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 999 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 999 13 14, g32p_row04_traceSegment_011_0999_0013, g32p_row04_traceSegment_011_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 972 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 972 27 27, g32p_row04_traceSegment_011_0972_0027, g32p_row04_traceSegment_011_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1026 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1026 13 14, g32p_row04_traceSegment_011_1026_0013, g32p_row04_traceSegment_011_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1053 13 14, g32p_row04_traceSegment_011_1053_0013, g32p_row04_traceSegment_011_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1026 27 27, g32p_row04_traceSegment_011_1026_0027, g32p_row04_traceSegment_011_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 972 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 972 54 54, g32p_row04_traceSegment_011_0972_0054, g32p_row04_traceSegment_011_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 864 216 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 864 108 108, g32p_row04_traceSegment_011_0864_0108, g32p_row04_traceSegment_011_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1093 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1080 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1080 13 14, g32p_row04_traceSegment_011_1080_0013, g32p_row04_traceSegment_011_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1107 13 14, g32p_row04_traceSegment_011_1107_0013, g32p_row04_traceSegment_011_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1080 27 27, g32p_row04_traceSegment_011_1080_0027, g32p_row04_traceSegment_011_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1134 13 14, g32p_row04_traceSegment_011_1134_0013, g32p_row04_traceSegment_011_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1161 13 14, g32p_row04_traceSegment_011_1161_0013, g32p_row04_traceSegment_011_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1134 27 27, g32p_row04_traceSegment_011_1134_0027, g32p_row04_traceSegment_011_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 1080 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1080 54 54, g32p_row04_traceSegment_011_1080_0054, g32p_row04_traceSegment_011_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1188 13 14, g32p_row04_traceSegment_011_1188_0013, g32p_row04_traceSegment_011_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1215 13 14, g32p_row04_traceSegment_011_1215_0013, g32p_row04_traceSegment_011_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1188 27 27, g32p_row04_traceSegment_011_1188_0027, g32p_row04_traceSegment_011_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1242 13 14, g32p_row04_traceSegment_011_1242_0013, g32p_row04_traceSegment_011_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1269 13 14, g32p_row04_traceSegment_011_1269_0013, g32p_row04_traceSegment_011_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1242 27 27, g32p_row04_traceSegment_011_1242_0027, g32p_row04_traceSegment_011_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1188 54 54, g32p_row04_traceSegment_011_1188_0054, g32p_row04_traceSegment_011_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1080 108 108, g32p_row04_traceSegment_011_1080_0108, g32p_row04_traceSegment_011_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_011 864 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 864 216 216, g32p_row04_traceSegment_011_0864_0216, g32p_row04_traceSegment_011_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1296 13 14, g32p_row04_traceSegment_011_1296_0013, g32p_row04_traceSegment_011_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1323 13 14, g32p_row04_traceSegment_011_1323_0013, g32p_row04_traceSegment_011_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1296 27 27, g32p_row04_traceSegment_011_1296_0027, g32p_row04_traceSegment_011_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1350 13 14, g32p_row04_traceSegment_011_1350_0013, g32p_row04_traceSegment_011_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1377 13 14, g32p_row04_traceSegment_011_1377_0013, g32p_row04_traceSegment_011_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1350 27 27, g32p_row04_traceSegment_011_1350_0027, g32p_row04_traceSegment_011_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1296 54 54, g32p_row04_traceSegment_011_1296_0054, g32p_row04_traceSegment_011_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1404 13 14, g32p_row04_traceSegment_011_1404_0013, g32p_row04_traceSegment_011_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1431 13 14, g32p_row04_traceSegment_011_1431_0013, g32p_row04_traceSegment_011_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1404 27 27, g32p_row04_traceSegment_011_1404_0027, g32p_row04_traceSegment_011_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1458 13 14, g32p_row04_traceSegment_011_1458_0013, g32p_row04_traceSegment_011_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1498 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1485 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1485 13 14, g32p_row04_traceSegment_011_1485_0013, g32p_row04_traceSegment_011_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1458 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1458 27 27, g32p_row04_traceSegment_011_1458_0027, g32p_row04_traceSegment_011_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 1404 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1404 54 54, g32p_row04_traceSegment_011_1404_0054, g32p_row04_traceSegment_011_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 1296 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1296 108 108, g32p_row04_traceSegment_011_1296_0108, g32p_row04_traceSegment_011_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1512 13 14, g32p_row04_traceSegment_011_1512_0013, g32p_row04_traceSegment_011_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1539 13 14, g32p_row04_traceSegment_011_1539_0013, g32p_row04_traceSegment_011_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1512 27 27, g32p_row04_traceSegment_011_1512_0027, g32p_row04_traceSegment_011_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1566 13 14, g32p_row04_traceSegment_011_1566_0013, g32p_row04_traceSegment_011_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1593 13 14, g32p_row04_traceSegment_011_1593_0013, g32p_row04_traceSegment_011_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1566 27 27, g32p_row04_traceSegment_011_1566_0027, g32p_row04_traceSegment_011_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1512 54 54, g32p_row04_traceSegment_011_1512_0054, g32p_row04_traceSegment_011_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1620 13 14, g32p_row04_traceSegment_011_1620_0013, g32p_row04_traceSegment_011_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1647 13 14, g32p_row04_traceSegment_011_1647_0013, g32p_row04_traceSegment_011_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1620 27 27, g32p_row04_traceSegment_011_1620_0027, g32p_row04_traceSegment_011_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1674 13 14, g32p_row04_traceSegment_011_1674_0013, g32p_row04_traceSegment_011_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_011 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_011 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_011_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_011 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1701 13 14, g32p_row04_traceSegment_011_1701_0013, g32p_row04_traceSegment_011_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_011 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1674 27 27, g32p_row04_traceSegment_011_1674_0027, g32p_row04_traceSegment_011_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_011 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1620 54 54, g32p_row04_traceSegment_011_1620_0054, g32p_row04_traceSegment_011_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_011 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1512 108 108, g32p_row04_traceSegment_011_1512_0108, g32p_row04_traceSegment_011_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_011_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_011 1296 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 1296 216 216, g32p_row04_traceSegment_011_1296_0216, g32p_row04_traceSegment_011_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_011 864 864 = [2, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 864 432 432, g32p_row04_traceSegment_011_0864_0432, g32p_row04_traceSegment_011_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_011_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_011 0 1728 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_011 0 864 864, g32p_row04_traceSegment_011_0000_0864, g32p_row04_traceSegment_011_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 11 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_011_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_013_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 13 14, g32p_row04_traceSegment_013_0000_0013, g32p_row04_traceSegment_013_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 27 13 14, g32p_row04_traceSegment_013_0027_0013, g32p_row04_traceSegment_013_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 27 27, g32p_row04_traceSegment_013_0000_0027, g32p_row04_traceSegment_013_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 54 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 54 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 54 13 14, g32p_row04_traceSegment_013_0054_0013, g32p_row04_traceSegment_013_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 81 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 94 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 81 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 81 13 14, g32p_row04_traceSegment_013_0081_0013, g32p_row04_traceSegment_013_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 54 54 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 54 27 27, g32p_row04_traceSegment_013_0054_0027, g32p_row04_traceSegment_013_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 0 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 54 54, g32p_row04_traceSegment_013_0000_0054, g32p_row04_traceSegment_013_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 108 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 121 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 108 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 108 13 14, g32p_row04_traceSegment_013_0108_0013, g32p_row04_traceSegment_013_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 135 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 135 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 135 13 14, g32p_row04_traceSegment_013_0135_0013, g32p_row04_traceSegment_013_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 108 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 108 27 27, g32p_row04_traceSegment_013_0108_0027, g32p_row04_traceSegment_013_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 162 13 14, g32p_row04_traceSegment_013_0162_0013, g32p_row04_traceSegment_013_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 189 13 14, g32p_row04_traceSegment_013_0189_0013, g32p_row04_traceSegment_013_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 162 27 27, g32p_row04_traceSegment_013_0162_0027, g32p_row04_traceSegment_013_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 108 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 108 54 54, g32p_row04_traceSegment_013_0108_0054, g32p_row04_traceSegment_013_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 0 216 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 108 108, g32p_row04_traceSegment_013_0000_0108, g32p_row04_traceSegment_013_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 216 13 14, g32p_row04_traceSegment_013_0216_0013, g32p_row04_traceSegment_013_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 243 13 14, g32p_row04_traceSegment_013_0243_0013, g32p_row04_traceSegment_013_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 216 27 27, g32p_row04_traceSegment_013_0216_0027, g32p_row04_traceSegment_013_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 270 13 14, g32p_row04_traceSegment_013_0270_0013, g32p_row04_traceSegment_013_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 297 13 14, g32p_row04_traceSegment_013_0297_0013, g32p_row04_traceSegment_013_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 270 27 27, g32p_row04_traceSegment_013_0270_0027, g32p_row04_traceSegment_013_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 216 54 54, g32p_row04_traceSegment_013_0216_0054, g32p_row04_traceSegment_013_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 324 13 14, g32p_row04_traceSegment_013_0324_0013, g32p_row04_traceSegment_013_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 351 13 14, g32p_row04_traceSegment_013_0351_0013, g32p_row04_traceSegment_013_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 324 27 27, g32p_row04_traceSegment_013_0324_0027, g32p_row04_traceSegment_013_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 378 13 14, g32p_row04_traceSegment_013_0378_0013, g32p_row04_traceSegment_013_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 405 13 14, g32p_row04_traceSegment_013_0405_0013, g32p_row04_traceSegment_013_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 378 27 27, g32p_row04_traceSegment_013_0378_0027, g32p_row04_traceSegment_013_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 324 54 54, g32p_row04_traceSegment_013_0324_0054, g32p_row04_traceSegment_013_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 216 108 108, g32p_row04_traceSegment_013_0216_0108, g32p_row04_traceSegment_013_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_013 0 432 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 216 216, g32p_row04_traceSegment_013_0000_0216, g32p_row04_traceSegment_013_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 432 13 14, g32p_row04_traceSegment_013_0432_0013, g32p_row04_traceSegment_013_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 459 13 14, g32p_row04_traceSegment_013_0459_0013, g32p_row04_traceSegment_013_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 432 27 27, g32p_row04_traceSegment_013_0432_0027, g32p_row04_traceSegment_013_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 486 13 14, g32p_row04_traceSegment_013_0486_0013, g32p_row04_traceSegment_013_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 526 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 513 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 513 13 14, g32p_row04_traceSegment_013_0513_0013, g32p_row04_traceSegment_013_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 486 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 486 27 27, g32p_row04_traceSegment_013_0486_0027, g32p_row04_traceSegment_013_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 432 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 432 54 54, g32p_row04_traceSegment_013_0432_0054, g32p_row04_traceSegment_013_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 553 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 540 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 540 13 14, g32p_row04_traceSegment_013_0540_0013, g32p_row04_traceSegment_013_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 567 13 14, g32p_row04_traceSegment_013_0567_0013, g32p_row04_traceSegment_013_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 540 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 540 27 27, g32p_row04_traceSegment_013_0540_0027, g32p_row04_traceSegment_013_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 594 13 14, g32p_row04_traceSegment_013_0594_0013, g32p_row04_traceSegment_013_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 621 13 14, g32p_row04_traceSegment_013_0621_0013, g32p_row04_traceSegment_013_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 594 27 27, g32p_row04_traceSegment_013_0594_0027, g32p_row04_traceSegment_013_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 540 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 540 54 54, g32p_row04_traceSegment_013_0540_0054, g32p_row04_traceSegment_013_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 432 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 432 108 108, g32p_row04_traceSegment_013_0432_0108, g32p_row04_traceSegment_013_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 648 13 14, g32p_row04_traceSegment_013_0648_0013, g32p_row04_traceSegment_013_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 675 13 14, g32p_row04_traceSegment_013_0675_0013, g32p_row04_traceSegment_013_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 648 27 27, g32p_row04_traceSegment_013_0648_0027, g32p_row04_traceSegment_013_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 702 13 14, g32p_row04_traceSegment_013_0702_0013, g32p_row04_traceSegment_013_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 742 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 729 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 729 13 14, g32p_row04_traceSegment_013_0729_0013, g32p_row04_traceSegment_013_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 702 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 702 27 27, g32p_row04_traceSegment_013_0702_0027, g32p_row04_traceSegment_013_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 648 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 648 54 54, g32p_row04_traceSegment_013_0648_0054, g32p_row04_traceSegment_013_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 756 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 769 14 = [0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 756 27 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 756 13 14, g32p_row04_traceSegment_013_0756_0013, g32p_row04_traceSegment_013_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 783 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 796 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 783 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 783 13 14, g32p_row04_traceSegment_013_0783_0013, g32p_row04_traceSegment_013_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 756 54 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 756 27 27, g32p_row04_traceSegment_013_0756_0027, g32p_row04_traceSegment_013_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 810 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 823 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 810 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 810 13 14, g32p_row04_traceSegment_013_0810_0013, g32p_row04_traceSegment_013_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 837 13 14, g32p_row04_traceSegment_013_0837_0013, g32p_row04_traceSegment_013_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 810 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 810 27 27, g32p_row04_traceSegment_013_0810_0027, g32p_row04_traceSegment_013_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 756 108 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 756 54 54, g32p_row04_traceSegment_013_0756_0054, g32p_row04_traceSegment_013_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 648 216 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 648 108 108, g32p_row04_traceSegment_013_0648_0108, g32p_row04_traceSegment_013_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_013 432 432 = [0, 23] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 432 216 216, g32p_row04_traceSegment_013_0432_0216, g32p_row04_traceSegment_013_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_013 0 864 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 432 432, g32p_row04_traceSegment_013_0000_0432, g32p_row04_traceSegment_013_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 864 13 14, g32p_row04_traceSegment_013_0864_0013, g32p_row04_traceSegment_013_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 891 13 14, g32p_row04_traceSegment_013_0891_0013, g32p_row04_traceSegment_013_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 864 27 27, g32p_row04_traceSegment_013_0864_0027, g32p_row04_traceSegment_013_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 918 13 14, g32p_row04_traceSegment_013_0918_0013, g32p_row04_traceSegment_013_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 945 13 14, g32p_row04_traceSegment_013_0945_0013, g32p_row04_traceSegment_013_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 918 27 27, g32p_row04_traceSegment_013_0918_0027, g32p_row04_traceSegment_013_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 864 54 54, g32p_row04_traceSegment_013_0864_0054, g32p_row04_traceSegment_013_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 972 13 14, g32p_row04_traceSegment_013_0972_0013, g32p_row04_traceSegment_013_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 999 13 14, g32p_row04_traceSegment_013_0999_0013, g32p_row04_traceSegment_013_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 972 27 27, g32p_row04_traceSegment_013_0972_0027, g32p_row04_traceSegment_013_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1026 13 14, g32p_row04_traceSegment_013_1026_0013, g32p_row04_traceSegment_013_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1053 13 14, g32p_row04_traceSegment_013_1053_0013, g32p_row04_traceSegment_013_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1026 27 27, g32p_row04_traceSegment_013_1026_0027, g32p_row04_traceSegment_013_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 972 54 54, g32p_row04_traceSegment_013_0972_0054, g32p_row04_traceSegment_013_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 864 108 108, g32p_row04_traceSegment_013_0864_0108, g32p_row04_traceSegment_013_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1080 13 14, g32p_row04_traceSegment_013_1080_0013, g32p_row04_traceSegment_013_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1107 13 14, g32p_row04_traceSegment_013_1107_0013, g32p_row04_traceSegment_013_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1080 27 27, g32p_row04_traceSegment_013_1080_0027, g32p_row04_traceSegment_013_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1134 13 14, g32p_row04_traceSegment_013_1134_0013, g32p_row04_traceSegment_013_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1161 13 14, g32p_row04_traceSegment_013_1161_0013, g32p_row04_traceSegment_013_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1134 27 27, g32p_row04_traceSegment_013_1134_0027, g32p_row04_traceSegment_013_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1080 54 54, g32p_row04_traceSegment_013_1080_0054, g32p_row04_traceSegment_013_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1188 13 14, g32p_row04_traceSegment_013_1188_0013, g32p_row04_traceSegment_013_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1215 13 14, g32p_row04_traceSegment_013_1215_0013, g32p_row04_traceSegment_013_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1188 27 27, g32p_row04_traceSegment_013_1188_0027, g32p_row04_traceSegment_013_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1242 13 14, g32p_row04_traceSegment_013_1242_0013, g32p_row04_traceSegment_013_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1269 13 14, g32p_row04_traceSegment_013_1269_0013, g32p_row04_traceSegment_013_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1242 27 27, g32p_row04_traceSegment_013_1242_0027, g32p_row04_traceSegment_013_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1188 54 54, g32p_row04_traceSegment_013_1188_0054, g32p_row04_traceSegment_013_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1080 108 108, g32p_row04_traceSegment_013_1080_0108, g32p_row04_traceSegment_013_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_013 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 864 216 216, g32p_row04_traceSegment_013_0864_0216, g32p_row04_traceSegment_013_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1296 13 14, g32p_row04_traceSegment_013_1296_0013, g32p_row04_traceSegment_013_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1323 13 14, g32p_row04_traceSegment_013_1323_0013, g32p_row04_traceSegment_013_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1296 27 27, g32p_row04_traceSegment_013_1296_0027, g32p_row04_traceSegment_013_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1350 13 14, g32p_row04_traceSegment_013_1350_0013, g32p_row04_traceSegment_013_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1377 13 14, g32p_row04_traceSegment_013_1377_0013, g32p_row04_traceSegment_013_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1350 27 27, g32p_row04_traceSegment_013_1350_0027, g32p_row04_traceSegment_013_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1296 54 54, g32p_row04_traceSegment_013_1296_0054, g32p_row04_traceSegment_013_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1404 13 14, g32p_row04_traceSegment_013_1404_0013, g32p_row04_traceSegment_013_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1431 13 14, g32p_row04_traceSegment_013_1431_0013, g32p_row04_traceSegment_013_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1404 27 27, g32p_row04_traceSegment_013_1404_0027, g32p_row04_traceSegment_013_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1458 13 14, g32p_row04_traceSegment_013_1458_0013, g32p_row04_traceSegment_013_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1485 13 14, g32p_row04_traceSegment_013_1485_0013, g32p_row04_traceSegment_013_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1458 27 27, g32p_row04_traceSegment_013_1458_0027, g32p_row04_traceSegment_013_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1404 54 54, g32p_row04_traceSegment_013_1404_0054, g32p_row04_traceSegment_013_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1296 108 108, g32p_row04_traceSegment_013_1296_0108, g32p_row04_traceSegment_013_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1512 13 14, g32p_row04_traceSegment_013_1512_0013, g32p_row04_traceSegment_013_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1539 13 14, g32p_row04_traceSegment_013_1539_0013, g32p_row04_traceSegment_013_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1512 27 27, g32p_row04_traceSegment_013_1512_0027, g32p_row04_traceSegment_013_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1579 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1566 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1566 13 14, g32p_row04_traceSegment_013_1566_0013, g32p_row04_traceSegment_013_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1606 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1593 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1593 13 14, g32p_row04_traceSegment_013_1593_0013, g32p_row04_traceSegment_013_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1566 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1566 27 27, g32p_row04_traceSegment_013_1566_0027, g32p_row04_traceSegment_013_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 1512 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1512 54 54, g32p_row04_traceSegment_013_1512_0054, g32p_row04_traceSegment_013_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1620 13 14, g32p_row04_traceSegment_013_1620_0013, g32p_row04_traceSegment_013_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1647 13 14, g32p_row04_traceSegment_013_1647_0013, g32p_row04_traceSegment_013_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1620 27 27, g32p_row04_traceSegment_013_1620_0027, g32p_row04_traceSegment_013_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1674 13 14, g32p_row04_traceSegment_013_1674_0013, g32p_row04_traceSegment_013_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_013 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_013 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_013_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_013 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1701 13 14, g32p_row04_traceSegment_013_1701_0013, g32p_row04_traceSegment_013_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_013 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1674 27 27, g32p_row04_traceSegment_013_1674_0027, g32p_row04_traceSegment_013_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_013 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1620 54 54, g32p_row04_traceSegment_013_1620_0054, g32p_row04_traceSegment_013_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_013 1512 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1512 108 108, g32p_row04_traceSegment_013_1512_0108, g32p_row04_traceSegment_013_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_013_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_013 1296 432 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 1296 216 216, g32p_row04_traceSegment_013_1296_0216, g32p_row04_traceSegment_013_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_013 864 864 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 864 432 432, g32p_row04_traceSegment_013_0864_0432, g32p_row04_traceSegment_013_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_013_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_013 0 1728 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_013 0 864 864, g32p_row04_traceSegment_013_0000_0864, g32p_row04_traceSegment_013_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 13 = [0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_013_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_015 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 15 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_015_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 13 14, g32p_row04_traceSegment_015_0000_0013, g32p_row04_traceSegment_015_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 27 13 14, g32p_row04_traceSegment_015_0027_0013, g32p_row04_traceSegment_015_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 27 27, g32p_row04_traceSegment_015_0000_0027, g32p_row04_traceSegment_015_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 54 13 14, g32p_row04_traceSegment_015_0054_0013, g32p_row04_traceSegment_015_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 81 13 14, g32p_row04_traceSegment_015_0081_0013, g32p_row04_traceSegment_015_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 54 27 27, g32p_row04_traceSegment_015_0054_0027, g32p_row04_traceSegment_015_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 54 54, g32p_row04_traceSegment_015_0000_0054, g32p_row04_traceSegment_015_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 108 13 14, g32p_row04_traceSegment_015_0108_0013, g32p_row04_traceSegment_015_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 135 13 14, g32p_row04_traceSegment_015_0135_0013, g32p_row04_traceSegment_015_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 108 27 27, g32p_row04_traceSegment_015_0108_0027, g32p_row04_traceSegment_015_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 162 13 14, g32p_row04_traceSegment_015_0162_0013, g32p_row04_traceSegment_015_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 189 13 14, g32p_row04_traceSegment_015_0189_0013, g32p_row04_traceSegment_015_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 162 27 27, g32p_row04_traceSegment_015_0162_0027, g32p_row04_traceSegment_015_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 108 54 54, g32p_row04_traceSegment_015_0108_0054, g32p_row04_traceSegment_015_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 108 108, g32p_row04_traceSegment_015_0000_0108, g32p_row04_traceSegment_015_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 216 13 14, g32p_row04_traceSegment_015_0216_0013, g32p_row04_traceSegment_015_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 243 13 14, g32p_row04_traceSegment_015_0243_0013, g32p_row04_traceSegment_015_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 216 27 27, g32p_row04_traceSegment_015_0216_0027, g32p_row04_traceSegment_015_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 270 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 283 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 270 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 270 13 14, g32p_row04_traceSegment_015_0270_0013, g32p_row04_traceSegment_015_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 297 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 297 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 297 13 14, g32p_row04_traceSegment_015_0297_0013, g32p_row04_traceSegment_015_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 270 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 270 27 27, g32p_row04_traceSegment_015_0270_0027, g32p_row04_traceSegment_015_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 216 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 216 54 54, g32p_row04_traceSegment_015_0216_0054, g32p_row04_traceSegment_015_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 337 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 324 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 324 13 14, g32p_row04_traceSegment_015_0324_0013, g32p_row04_traceSegment_015_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 351 13 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 364 14 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 351 27 = [2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 351 13 14, g32p_row04_traceSegment_015_0351_0013, g32p_row04_traceSegment_015_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 324 54 = [2, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 324 27 27, g32p_row04_traceSegment_015_0324_0027, g32p_row04_traceSegment_015_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 378 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 391 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 378 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 378 13 14, g32p_row04_traceSegment_015_0378_0013, g32p_row04_traceSegment_015_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 405 13 = [2, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 405 27 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 405 13 14, g32p_row04_traceSegment_015_0405_0013, g32p_row04_traceSegment_015_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 378 54 = [2, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 378 27 27, g32p_row04_traceSegment_015_0378_0027, g32p_row04_traceSegment_015_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 324 108 = [4, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 324 54 54, g32p_row04_traceSegment_015_0324_0054, g32p_row04_traceSegment_015_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 216 216 = [8, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 216 108 108, g32p_row04_traceSegment_015_0216_0108, g32p_row04_traceSegment_015_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_015 0 432 = [8, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 216 216, g32p_row04_traceSegment_015_0000_0216, g32p_row04_traceSegment_015_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 432 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 445 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 432 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 432 13 14, g32p_row04_traceSegment_015_0432_0013, g32p_row04_traceSegment_015_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 459 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 472 14 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 459 27 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 459 13 14, g32p_row04_traceSegment_015_0459_0013, g32p_row04_traceSegment_015_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 432 54 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 432 27 27, g32p_row04_traceSegment_015_0432_0027, g32p_row04_traceSegment_015_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 486 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 486 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 486 13 14, g32p_row04_traceSegment_015_0486_0013, g32p_row04_traceSegment_015_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 513 13 14, g32p_row04_traceSegment_015_0513_0013, g32p_row04_traceSegment_015_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 486 54 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 486 27 27, g32p_row04_traceSegment_015_0486_0027, g32p_row04_traceSegment_015_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 432 108 = [5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 432 54 54, g32p_row04_traceSegment_015_0432_0054, g32p_row04_traceSegment_015_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 540 13 14, g32p_row04_traceSegment_015_0540_0013, g32p_row04_traceSegment_015_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 567 13 14, g32p_row04_traceSegment_015_0567_0013, g32p_row04_traceSegment_015_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 540 27 27, g32p_row04_traceSegment_015_0540_0027, g32p_row04_traceSegment_015_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 594 13 14, g32p_row04_traceSegment_015_0594_0013, g32p_row04_traceSegment_015_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 621 13 14, g32p_row04_traceSegment_015_0621_0013, g32p_row04_traceSegment_015_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 594 27 27, g32p_row04_traceSegment_015_0594_0027, g32p_row04_traceSegment_015_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 540 54 54, g32p_row04_traceSegment_015_0540_0054, g32p_row04_traceSegment_015_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 432 216 = [5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 432 108 108, g32p_row04_traceSegment_015_0432_0108, g32p_row04_traceSegment_015_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 648 13 14, g32p_row04_traceSegment_015_0648_0013, g32p_row04_traceSegment_015_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 675 13 14, g32p_row04_traceSegment_015_0675_0013, g32p_row04_traceSegment_015_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 648 27 27, g32p_row04_traceSegment_015_0648_0027, g32p_row04_traceSegment_015_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 702 13 14, g32p_row04_traceSegment_015_0702_0013, g32p_row04_traceSegment_015_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 729 13 14, g32p_row04_traceSegment_015_0729_0013, g32p_row04_traceSegment_015_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 702 27 27, g32p_row04_traceSegment_015_0702_0027, g32p_row04_traceSegment_015_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 648 54 54, g32p_row04_traceSegment_015_0648_0054, g32p_row04_traceSegment_015_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 756 13 14, g32p_row04_traceSegment_015_0756_0013, g32p_row04_traceSegment_015_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 783 13 14, g32p_row04_traceSegment_015_0783_0013, g32p_row04_traceSegment_015_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 756 27 27, g32p_row04_traceSegment_015_0756_0027, g32p_row04_traceSegment_015_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 810 13 14, g32p_row04_traceSegment_015_0810_0013, g32p_row04_traceSegment_015_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 837 13 14, g32p_row04_traceSegment_015_0837_0013, g32p_row04_traceSegment_015_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 810 27 27, g32p_row04_traceSegment_015_0810_0027, g32p_row04_traceSegment_015_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 756 54 54, g32p_row04_traceSegment_015_0756_0054, g32p_row04_traceSegment_015_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 648 108 108, g32p_row04_traceSegment_015_0648_0108, g32p_row04_traceSegment_015_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_015 432 432 = [5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 432 216 216, g32p_row04_traceSegment_015_0432_0216, g32p_row04_traceSegment_015_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_015 0 864 = [13, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 432 432, g32p_row04_traceSegment_015_0000_0432, g32p_row04_traceSegment_015_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 864 13 14, g32p_row04_traceSegment_015_0864_0013, g32p_row04_traceSegment_015_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 891 13 14, g32p_row04_traceSegment_015_0891_0013, g32p_row04_traceSegment_015_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 864 27 27, g32p_row04_traceSegment_015_0864_0027, g32p_row04_traceSegment_015_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 918 13 14, g32p_row04_traceSegment_015_0918_0013, g32p_row04_traceSegment_015_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 945 13 14, g32p_row04_traceSegment_015_0945_0013, g32p_row04_traceSegment_015_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 918 27 27, g32p_row04_traceSegment_015_0918_0027, g32p_row04_traceSegment_015_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 864 54 54, g32p_row04_traceSegment_015_0864_0054, g32p_row04_traceSegment_015_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 972 13 14, g32p_row04_traceSegment_015_0972_0013, g32p_row04_traceSegment_015_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 999 13 14, g32p_row04_traceSegment_015_0999_0013, g32p_row04_traceSegment_015_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 972 27 27, g32p_row04_traceSegment_015_0972_0027, g32p_row04_traceSegment_015_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1026 13 14, g32p_row04_traceSegment_015_1026_0013, g32p_row04_traceSegment_015_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1053 13 14, g32p_row04_traceSegment_015_1053_0013, g32p_row04_traceSegment_015_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1026 27 27, g32p_row04_traceSegment_015_1026_0027, g32p_row04_traceSegment_015_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 972 54 54, g32p_row04_traceSegment_015_0972_0054, g32p_row04_traceSegment_015_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 864 108 108, g32p_row04_traceSegment_015_0864_0108, g32p_row04_traceSegment_015_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1080 13 14, g32p_row04_traceSegment_015_1080_0013, g32p_row04_traceSegment_015_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1107 13 14, g32p_row04_traceSegment_015_1107_0013, g32p_row04_traceSegment_015_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1080 27 27, g32p_row04_traceSegment_015_1080_0027, g32p_row04_traceSegment_015_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1134 13 14, g32p_row04_traceSegment_015_1134_0013, g32p_row04_traceSegment_015_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1161 13 14, g32p_row04_traceSegment_015_1161_0013, g32p_row04_traceSegment_015_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1134 27 27, g32p_row04_traceSegment_015_1134_0027, g32p_row04_traceSegment_015_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1080 54 54, g32p_row04_traceSegment_015_1080_0054, g32p_row04_traceSegment_015_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1188 13 14, g32p_row04_traceSegment_015_1188_0013, g32p_row04_traceSegment_015_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1215 13 14, g32p_row04_traceSegment_015_1215_0013, g32p_row04_traceSegment_015_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1188 27 27, g32p_row04_traceSegment_015_1188_0027, g32p_row04_traceSegment_015_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1242 13 14, g32p_row04_traceSegment_015_1242_0013, g32p_row04_traceSegment_015_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1282 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1269 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1269 13 14, g32p_row04_traceSegment_015_1269_0013, g32p_row04_traceSegment_015_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1242 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1242 27 27, g32p_row04_traceSegment_015_1242_0027, g32p_row04_traceSegment_015_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 1188 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1188 54 54, g32p_row04_traceSegment_015_1188_0054, g32p_row04_traceSegment_015_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 1080 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1080 108 108, g32p_row04_traceSegment_015_1080_0108, g32p_row04_traceSegment_015_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_015 864 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 864 216 216, g32p_row04_traceSegment_015_0864_0216, g32p_row04_traceSegment_015_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1296 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1296 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1296 13 14, g32p_row04_traceSegment_015_1296_0013, g32p_row04_traceSegment_015_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1323 13 14, g32p_row04_traceSegment_015_1323_0013, g32p_row04_traceSegment_015_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1296 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1296 27 27, g32p_row04_traceSegment_015_1296_0027, g32p_row04_traceSegment_015_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1350 13 14, g32p_row04_traceSegment_015_1350_0013, g32p_row04_traceSegment_015_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1377 13 14, g32p_row04_traceSegment_015_1377_0013, g32p_row04_traceSegment_015_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1350 27 27, g32p_row04_traceSegment_015_1350_0027, g32p_row04_traceSegment_015_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 1296 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1296 54 54, g32p_row04_traceSegment_015_1296_0054, g32p_row04_traceSegment_015_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1404 13 14, g32p_row04_traceSegment_015_1404_0013, g32p_row04_traceSegment_015_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1431 13 14, g32p_row04_traceSegment_015_1431_0013, g32p_row04_traceSegment_015_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1404 27 27, g32p_row04_traceSegment_015_1404_0027, g32p_row04_traceSegment_015_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1458 13 14, g32p_row04_traceSegment_015_1458_0013, g32p_row04_traceSegment_015_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1485 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1498 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1485 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1485 13 14, g32p_row04_traceSegment_015_1485_0013, g32p_row04_traceSegment_015_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1458 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1458 27 27, g32p_row04_traceSegment_015_1458_0027, g32p_row04_traceSegment_015_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 1404 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1404 54 54, g32p_row04_traceSegment_015_1404_0054, g32p_row04_traceSegment_015_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 1296 216 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1296 108 108, g32p_row04_traceSegment_015_1296_0108, g32p_row04_traceSegment_015_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1512 13 14, g32p_row04_traceSegment_015_1512_0013, g32p_row04_traceSegment_015_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1539 13 14, g32p_row04_traceSegment_015_1539_0013, g32p_row04_traceSegment_015_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1512 27 27, g32p_row04_traceSegment_015_1512_0027, g32p_row04_traceSegment_015_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1566 13 14, g32p_row04_traceSegment_015_1566_0013, g32p_row04_traceSegment_015_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1593 13 14, g32p_row04_traceSegment_015_1593_0013, g32p_row04_traceSegment_015_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1566 27 27, g32p_row04_traceSegment_015_1566_0027, g32p_row04_traceSegment_015_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1512 54 54, g32p_row04_traceSegment_015_1512_0054, g32p_row04_traceSegment_015_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1620 13 14, g32p_row04_traceSegment_015_1620_0013, g32p_row04_traceSegment_015_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1647 13 14, g32p_row04_traceSegment_015_1647_0013, g32p_row04_traceSegment_015_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1620 27 27, g32p_row04_traceSegment_015_1620_0027, g32p_row04_traceSegment_015_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1674 13 14, g32p_row04_traceSegment_015_1674_0013, g32p_row04_traceSegment_015_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_015 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_015 1714 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_015_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_015 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1701 13 14, g32p_row04_traceSegment_015_1701_0013, g32p_row04_traceSegment_015_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_015 1674 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1674 27 27, g32p_row04_traceSegment_015_1674_0027, g32p_row04_traceSegment_015_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_015 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1620 54 54, g32p_row04_traceSegment_015_1620_0054, g32p_row04_traceSegment_015_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_015 1512 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1512 108 108, g32p_row04_traceSegment_015_1512_0108, g32p_row04_traceSegment_015_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_015_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_015 1296 432 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 1296 216 216, g32p_row04_traceSegment_015_1296_0216, g32p_row04_traceSegment_015_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_015 864 864 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 864 432 432, g32p_row04_traceSegment_015_0864_0432, g32p_row04_traceSegment_015_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_015_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_015 0 1728 = [16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_015 0 864 864, g32p_row04_traceSegment_015_0000_0864, g32p_row04_traceSegment_015_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 15 = [16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_015_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_017 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 17 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_017_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 13 14, g32p_row04_traceSegment_017_0000_0013, g32p_row04_traceSegment_017_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 27 13 14, g32p_row04_traceSegment_017_0027_0013, g32p_row04_traceSegment_017_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 27 27, g32p_row04_traceSegment_017_0000_0027, g32p_row04_traceSegment_017_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 54 13 14, g32p_row04_traceSegment_017_0054_0013, g32p_row04_traceSegment_017_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 81 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 94 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 81 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 81 13 14, g32p_row04_traceSegment_017_0081_0013, g32p_row04_traceSegment_017_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 54 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 54 27 27, g32p_row04_traceSegment_017_0054_0027, g32p_row04_traceSegment_017_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 0 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 54 54, g32p_row04_traceSegment_017_0000_0054, g32p_row04_traceSegment_017_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 108 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 121 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 108 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 108 13 14, g32p_row04_traceSegment_017_0108_0013, g32p_row04_traceSegment_017_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 135 13 14, g32p_row04_traceSegment_017_0135_0013, g32p_row04_traceSegment_017_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 108 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 108 27 27, g32p_row04_traceSegment_017_0108_0027, g32p_row04_traceSegment_017_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 162 13 14, g32p_row04_traceSegment_017_0162_0013, g32p_row04_traceSegment_017_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 189 13 14, g32p_row04_traceSegment_017_0189_0013, g32p_row04_traceSegment_017_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 162 27 27, g32p_row04_traceSegment_017_0162_0027, g32p_row04_traceSegment_017_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 108 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 108 54 54, g32p_row04_traceSegment_017_0108_0054, g32p_row04_traceSegment_017_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 0 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 108 108, g32p_row04_traceSegment_017_0000_0108, g32p_row04_traceSegment_017_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 216 13 14, g32p_row04_traceSegment_017_0216_0013, g32p_row04_traceSegment_017_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 243 13 14, g32p_row04_traceSegment_017_0243_0013, g32p_row04_traceSegment_017_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 216 27 27, g32p_row04_traceSegment_017_0216_0027, g32p_row04_traceSegment_017_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 270 13 14, g32p_row04_traceSegment_017_0270_0013, g32p_row04_traceSegment_017_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 297 13 14, g32p_row04_traceSegment_017_0297_0013, g32p_row04_traceSegment_017_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 270 27 27, g32p_row04_traceSegment_017_0270_0027, g32p_row04_traceSegment_017_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 216 54 54, g32p_row04_traceSegment_017_0216_0054, g32p_row04_traceSegment_017_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 324 13 14, g32p_row04_traceSegment_017_0324_0013, g32p_row04_traceSegment_017_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 351 13 14, g32p_row04_traceSegment_017_0351_0013, g32p_row04_traceSegment_017_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 324 27 27, g32p_row04_traceSegment_017_0324_0027, g32p_row04_traceSegment_017_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 378 13 14, g32p_row04_traceSegment_017_0378_0013, g32p_row04_traceSegment_017_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 405 13 14, g32p_row04_traceSegment_017_0405_0013, g32p_row04_traceSegment_017_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 378 27 27, g32p_row04_traceSegment_017_0378_0027, g32p_row04_traceSegment_017_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 324 54 54, g32p_row04_traceSegment_017_0324_0054, g32p_row04_traceSegment_017_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 216 108 108, g32p_row04_traceSegment_017_0216_0108, g32p_row04_traceSegment_017_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_017 0 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 216 216, g32p_row04_traceSegment_017_0000_0216, g32p_row04_traceSegment_017_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 432 13 14, g32p_row04_traceSegment_017_0432_0013, g32p_row04_traceSegment_017_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 459 13 14, g32p_row04_traceSegment_017_0459_0013, g32p_row04_traceSegment_017_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 432 27 27, g32p_row04_traceSegment_017_0432_0027, g32p_row04_traceSegment_017_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 486 13 14, g32p_row04_traceSegment_017_0486_0013, g32p_row04_traceSegment_017_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 526 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 513 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 513 13 14, g32p_row04_traceSegment_017_0513_0013, g32p_row04_traceSegment_017_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 486 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 486 27 27, g32p_row04_traceSegment_017_0486_0027, g32p_row04_traceSegment_017_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 432 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 432 54 54, g32p_row04_traceSegment_017_0432_0054, g32p_row04_traceSegment_017_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 553 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 540 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 540 13 14, g32p_row04_traceSegment_017_0540_0013, g32p_row04_traceSegment_017_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 567 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 567 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 567 13 14, g32p_row04_traceSegment_017_0567_0013, g32p_row04_traceSegment_017_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 540 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 540 27 27, g32p_row04_traceSegment_017_0540_0027, g32p_row04_traceSegment_017_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 594 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 607 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 594 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 594 13 14, g32p_row04_traceSegment_017_0594_0013, g32p_row04_traceSegment_017_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 634 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 621 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 621 13 14, g32p_row04_traceSegment_017_0621_0013, g32p_row04_traceSegment_017_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 594 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 594 27 27, g32p_row04_traceSegment_017_0594_0027, g32p_row04_traceSegment_017_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 540 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 540 54 54, g32p_row04_traceSegment_017_0540_0054, g32p_row04_traceSegment_017_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 432 216 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 432 108 108, g32p_row04_traceSegment_017_0432_0108, g32p_row04_traceSegment_017_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 648 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 648 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 648 13 14, g32p_row04_traceSegment_017_0648_0013, g32p_row04_traceSegment_017_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 675 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 675 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 675 13 14, g32p_row04_traceSegment_017_0675_0013, g32p_row04_traceSegment_017_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 648 54 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 648 27 27, g32p_row04_traceSegment_017_0648_0027, g32p_row04_traceSegment_017_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 702 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 702 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 702 13 14, g32p_row04_traceSegment_017_0702_0013, g32p_row04_traceSegment_017_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 742 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 729 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 729 13 14, g32p_row04_traceSegment_017_0729_0013, g32p_row04_traceSegment_017_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 702 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 702 27 27, g32p_row04_traceSegment_017_0702_0027, g32p_row04_traceSegment_017_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 648 108 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 648 54 54, g32p_row04_traceSegment_017_0648_0054, g32p_row04_traceSegment_017_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 756 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 769 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 756 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 756 13 14, g32p_row04_traceSegment_017_0756_0013, g32p_row04_traceSegment_017_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 783 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 796 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 783 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 783 13 14, g32p_row04_traceSegment_017_0783_0013, g32p_row04_traceSegment_017_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 756 54 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 756 27 27, g32p_row04_traceSegment_017_0756_0027, g32p_row04_traceSegment_017_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 810 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 823 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 810 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 810 13 14, g32p_row04_traceSegment_017_0810_0013, g32p_row04_traceSegment_017_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 837 13 14, g32p_row04_traceSegment_017_0837_0013, g32p_row04_traceSegment_017_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 810 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 810 27 27, g32p_row04_traceSegment_017_0810_0027, g32p_row04_traceSegment_017_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 756 108 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 756 54 54, g32p_row04_traceSegment_017_0756_0054, g32p_row04_traceSegment_017_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 648 216 = [0, 1, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 648 108 108, g32p_row04_traceSegment_017_0648_0108, g32p_row04_traceSegment_017_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_017 432 432 = [0, 8, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 432 216 216, g32p_row04_traceSegment_017_0432_0216, g32p_row04_traceSegment_017_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_017 0 864 = [0, 8, 23] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 432 432, g32p_row04_traceSegment_017_0000_0432, g32p_row04_traceSegment_017_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 864 13 14, g32p_row04_traceSegment_017_0864_0013, g32p_row04_traceSegment_017_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 891 13 14, g32p_row04_traceSegment_017_0891_0013, g32p_row04_traceSegment_017_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 864 27 27, g32p_row04_traceSegment_017_0864_0027, g32p_row04_traceSegment_017_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 918 13 14, g32p_row04_traceSegment_017_0918_0013, g32p_row04_traceSegment_017_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 945 13 14, g32p_row04_traceSegment_017_0945_0013, g32p_row04_traceSegment_017_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 918 27 27, g32p_row04_traceSegment_017_0918_0027, g32p_row04_traceSegment_017_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 864 54 54, g32p_row04_traceSegment_017_0864_0054, g32p_row04_traceSegment_017_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 972 13 14, g32p_row04_traceSegment_017_0972_0013, g32p_row04_traceSegment_017_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 999 13 14, g32p_row04_traceSegment_017_0999_0013, g32p_row04_traceSegment_017_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 972 27 27, g32p_row04_traceSegment_017_0972_0027, g32p_row04_traceSegment_017_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1026 13 14, g32p_row04_traceSegment_017_1026_0013, g32p_row04_traceSegment_017_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1053 13 14, g32p_row04_traceSegment_017_1053_0013, g32p_row04_traceSegment_017_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1026 27 27, g32p_row04_traceSegment_017_1026_0027, g32p_row04_traceSegment_017_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 972 54 54, g32p_row04_traceSegment_017_0972_0054, g32p_row04_traceSegment_017_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 864 108 108, g32p_row04_traceSegment_017_0864_0108, g32p_row04_traceSegment_017_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1080 13 14, g32p_row04_traceSegment_017_1080_0013, g32p_row04_traceSegment_017_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1107 13 14, g32p_row04_traceSegment_017_1107_0013, g32p_row04_traceSegment_017_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1080 27 27, g32p_row04_traceSegment_017_1080_0027, g32p_row04_traceSegment_017_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1134 13 14, g32p_row04_traceSegment_017_1134_0013, g32p_row04_traceSegment_017_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1161 13 14, g32p_row04_traceSegment_017_1161_0013, g32p_row04_traceSegment_017_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1134 27 27, g32p_row04_traceSegment_017_1134_0027, g32p_row04_traceSegment_017_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1080 54 54, g32p_row04_traceSegment_017_1080_0054, g32p_row04_traceSegment_017_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1188 13 14, g32p_row04_traceSegment_017_1188_0013, g32p_row04_traceSegment_017_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1215 13 14, g32p_row04_traceSegment_017_1215_0013, g32p_row04_traceSegment_017_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1188 27 27, g32p_row04_traceSegment_017_1188_0027, g32p_row04_traceSegment_017_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1242 13 14, g32p_row04_traceSegment_017_1242_0013, g32p_row04_traceSegment_017_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1269 13 14, g32p_row04_traceSegment_017_1269_0013, g32p_row04_traceSegment_017_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1242 27 27, g32p_row04_traceSegment_017_1242_0027, g32p_row04_traceSegment_017_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1188 54 54, g32p_row04_traceSegment_017_1188_0054, g32p_row04_traceSegment_017_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1080 108 108, g32p_row04_traceSegment_017_1080_0108, g32p_row04_traceSegment_017_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_017 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 864 216 216, g32p_row04_traceSegment_017_0864_0216, g32p_row04_traceSegment_017_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1296 13 14, g32p_row04_traceSegment_017_1296_0013, g32p_row04_traceSegment_017_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1323 13 14, g32p_row04_traceSegment_017_1323_0013, g32p_row04_traceSegment_017_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1296 27 27, g32p_row04_traceSegment_017_1296_0027, g32p_row04_traceSegment_017_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1350 13 14, g32p_row04_traceSegment_017_1350_0013, g32p_row04_traceSegment_017_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1377 13 14, g32p_row04_traceSegment_017_1377_0013, g32p_row04_traceSegment_017_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1350 27 27, g32p_row04_traceSegment_017_1350_0027, g32p_row04_traceSegment_017_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1296 54 54, g32p_row04_traceSegment_017_1296_0054, g32p_row04_traceSegment_017_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1404 13 14, g32p_row04_traceSegment_017_1404_0013, g32p_row04_traceSegment_017_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1431 13 14, g32p_row04_traceSegment_017_1431_0013, g32p_row04_traceSegment_017_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1404 27 27, g32p_row04_traceSegment_017_1404_0027, g32p_row04_traceSegment_017_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1458 13 14, g32p_row04_traceSegment_017_1458_0013, g32p_row04_traceSegment_017_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1485 13 14, g32p_row04_traceSegment_017_1485_0013, g32p_row04_traceSegment_017_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1458 27 27, g32p_row04_traceSegment_017_1458_0027, g32p_row04_traceSegment_017_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1404 54 54, g32p_row04_traceSegment_017_1404_0054, g32p_row04_traceSegment_017_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1296 108 108, g32p_row04_traceSegment_017_1296_0108, g32p_row04_traceSegment_017_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1512 13 = [0, 6] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1525 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1512 27 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1512 13 14, g32p_row04_traceSegment_017_1512_0013, g32p_row04_traceSegment_017_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1539 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1539 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1539 13 14, g32p_row04_traceSegment_017_1539_0013, g32p_row04_traceSegment_017_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1512 54 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1512 27 27, g32p_row04_traceSegment_017_1512_0027, g32p_row04_traceSegment_017_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1566 13 14, g32p_row04_traceSegment_017_1566_0013, g32p_row04_traceSegment_017_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1593 13 14, g32p_row04_traceSegment_017_1593_0013, g32p_row04_traceSegment_017_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1566 27 27, g32p_row04_traceSegment_017_1566_0027, g32p_row04_traceSegment_017_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 1512 108 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1512 54 54, g32p_row04_traceSegment_017_1512_0054, g32p_row04_traceSegment_017_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1620 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1633 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1620 27 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1620 13 14, g32p_row04_traceSegment_017_1620_0013, g32p_row04_traceSegment_017_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1647 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1660 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1647 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1647 13 14, g32p_row04_traceSegment_017_1647_0013, g32p_row04_traceSegment_017_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1620 54 = [0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1620 27 27, g32p_row04_traceSegment_017_1620_0027, g32p_row04_traceSegment_017_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1674 13 14, g32p_row04_traceSegment_017_1674_0013, g32p_row04_traceSegment_017_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_017 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_017 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_017_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_017 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1701 13 14, g32p_row04_traceSegment_017_1701_0013, g32p_row04_traceSegment_017_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_017 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1674 27 27, g32p_row04_traceSegment_017_1674_0027, g32p_row04_traceSegment_017_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_017 1620 108 = [0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1620 54 54, g32p_row04_traceSegment_017_1620_0054, g32p_row04_traceSegment_017_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_017 1512 216 = [0, 16, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1512 108 108, g32p_row04_traceSegment_017_1512_0108, g32p_row04_traceSegment_017_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_017_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_017 1296 432 = [0, 16, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 1296 216 216, g32p_row04_traceSegment_017_1296_0216, g32p_row04_traceSegment_017_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_017 864 864 = [0, 16, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 864 432 432, g32p_row04_traceSegment_017_0864_0432, g32p_row04_traceSegment_017_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_017_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_017 0 1728 = [0, 24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_017 0 864 864, g32p_row04_traceSegment_017_0000_0864, g32p_row04_traceSegment_017_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 17 = [0, 24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_017_0000_1728

end HodgeLean.Foundations.Program

end
end
