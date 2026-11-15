import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0337

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_031 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 31 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_031_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 13 14, g32p_row04_traceSegment_031_0000_0013, g32p_row04_traceSegment_031_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 27 13 14, g32p_row04_traceSegment_031_0027_0013, g32p_row04_traceSegment_031_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 27 27, g32p_row04_traceSegment_031_0000_0027, g32p_row04_traceSegment_031_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 54 13 14, g32p_row04_traceSegment_031_0054_0013, g32p_row04_traceSegment_031_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 81 13 14, g32p_row04_traceSegment_031_0081_0013, g32p_row04_traceSegment_031_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 54 27 27, g32p_row04_traceSegment_031_0054_0027, g32p_row04_traceSegment_031_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 54 54, g32p_row04_traceSegment_031_0000_0054, g32p_row04_traceSegment_031_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 108 13 14, g32p_row04_traceSegment_031_0108_0013, g32p_row04_traceSegment_031_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 135 13 14, g32p_row04_traceSegment_031_0135_0013, g32p_row04_traceSegment_031_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 108 27 27, g32p_row04_traceSegment_031_0108_0027, g32p_row04_traceSegment_031_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 162 13 14, g32p_row04_traceSegment_031_0162_0013, g32p_row04_traceSegment_031_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 189 13 14, g32p_row04_traceSegment_031_0189_0013, g32p_row04_traceSegment_031_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 162 27 27, g32p_row04_traceSegment_031_0162_0027, g32p_row04_traceSegment_031_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 108 54 54, g32p_row04_traceSegment_031_0108_0054, g32p_row04_traceSegment_031_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 108 108, g32p_row04_traceSegment_031_0000_0108, g32p_row04_traceSegment_031_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 216 13 14, g32p_row04_traceSegment_031_0216_0013, g32p_row04_traceSegment_031_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 243 13 14, g32p_row04_traceSegment_031_0243_0013, g32p_row04_traceSegment_031_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 216 27 27, g32p_row04_traceSegment_031_0216_0027, g32p_row04_traceSegment_031_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 270 13 14, g32p_row04_traceSegment_031_0270_0013, g32p_row04_traceSegment_031_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 297 13 14, g32p_row04_traceSegment_031_0297_0013, g32p_row04_traceSegment_031_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 270 27 27, g32p_row04_traceSegment_031_0270_0027, g32p_row04_traceSegment_031_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 216 54 54, g32p_row04_traceSegment_031_0216_0054, g32p_row04_traceSegment_031_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 324 13 14, g32p_row04_traceSegment_031_0324_0013, g32p_row04_traceSegment_031_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 351 13 14, g32p_row04_traceSegment_031_0351_0013, g32p_row04_traceSegment_031_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 324 27 27, g32p_row04_traceSegment_031_0324_0027, g32p_row04_traceSegment_031_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 378 13 14, g32p_row04_traceSegment_031_0378_0013, g32p_row04_traceSegment_031_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 405 13 14, g32p_row04_traceSegment_031_0405_0013, g32p_row04_traceSegment_031_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 378 27 27, g32p_row04_traceSegment_031_0378_0027, g32p_row04_traceSegment_031_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 324 54 54, g32p_row04_traceSegment_031_0324_0054, g32p_row04_traceSegment_031_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 216 108 108, g32p_row04_traceSegment_031_0216_0108, g32p_row04_traceSegment_031_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_031 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 216 216, g32p_row04_traceSegment_031_0000_0216, g32p_row04_traceSegment_031_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 432 13 14, g32p_row04_traceSegment_031_0432_0013, g32p_row04_traceSegment_031_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 459 13 14, g32p_row04_traceSegment_031_0459_0013, g32p_row04_traceSegment_031_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 432 27 27, g32p_row04_traceSegment_031_0432_0027, g32p_row04_traceSegment_031_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 486 13 14, g32p_row04_traceSegment_031_0486_0013, g32p_row04_traceSegment_031_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 513 13 14, g32p_row04_traceSegment_031_0513_0013, g32p_row04_traceSegment_031_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 486 27 27, g32p_row04_traceSegment_031_0486_0027, g32p_row04_traceSegment_031_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 432 54 54, g32p_row04_traceSegment_031_0432_0054, g32p_row04_traceSegment_031_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 540 13 14, g32p_row04_traceSegment_031_0540_0013, g32p_row04_traceSegment_031_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 567 13 14, g32p_row04_traceSegment_031_0567_0013, g32p_row04_traceSegment_031_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 540 27 27, g32p_row04_traceSegment_031_0540_0027, g32p_row04_traceSegment_031_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 594 13 14, g32p_row04_traceSegment_031_0594_0013, g32p_row04_traceSegment_031_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 621 13 14, g32p_row04_traceSegment_031_0621_0013, g32p_row04_traceSegment_031_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 594 27 27, g32p_row04_traceSegment_031_0594_0027, g32p_row04_traceSegment_031_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 540 54 54, g32p_row04_traceSegment_031_0540_0054, g32p_row04_traceSegment_031_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 432 108 108, g32p_row04_traceSegment_031_0432_0108, g32p_row04_traceSegment_031_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 648 13 14, g32p_row04_traceSegment_031_0648_0013, g32p_row04_traceSegment_031_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 675 13 14, g32p_row04_traceSegment_031_0675_0013, g32p_row04_traceSegment_031_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 648 27 27, g32p_row04_traceSegment_031_0648_0027, g32p_row04_traceSegment_031_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 702 13 14, g32p_row04_traceSegment_031_0702_0013, g32p_row04_traceSegment_031_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 729 13 14, g32p_row04_traceSegment_031_0729_0013, g32p_row04_traceSegment_031_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 702 27 27, g32p_row04_traceSegment_031_0702_0027, g32p_row04_traceSegment_031_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 648 54 54, g32p_row04_traceSegment_031_0648_0054, g32p_row04_traceSegment_031_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 756 13 14, g32p_row04_traceSegment_031_0756_0013, g32p_row04_traceSegment_031_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 783 13 14, g32p_row04_traceSegment_031_0783_0013, g32p_row04_traceSegment_031_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 756 27 27, g32p_row04_traceSegment_031_0756_0027, g32p_row04_traceSegment_031_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 810 13 14, g32p_row04_traceSegment_031_0810_0013, g32p_row04_traceSegment_031_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 837 13 14, g32p_row04_traceSegment_031_0837_0013, g32p_row04_traceSegment_031_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 810 27 27, g32p_row04_traceSegment_031_0810_0027, g32p_row04_traceSegment_031_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 756 54 54, g32p_row04_traceSegment_031_0756_0054, g32p_row04_traceSegment_031_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 648 108 108, g32p_row04_traceSegment_031_0648_0108, g32p_row04_traceSegment_031_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_031 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 432 216 216, g32p_row04_traceSegment_031_0432_0216, g32p_row04_traceSegment_031_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_031 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 432 432, g32p_row04_traceSegment_031_0000_0432, g32p_row04_traceSegment_031_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 864 13 14, g32p_row04_traceSegment_031_0864_0013, g32p_row04_traceSegment_031_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 891 13 14, g32p_row04_traceSegment_031_0891_0013, g32p_row04_traceSegment_031_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 864 27 27, g32p_row04_traceSegment_031_0864_0027, g32p_row04_traceSegment_031_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 918 13 14, g32p_row04_traceSegment_031_0918_0013, g32p_row04_traceSegment_031_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 945 13 14, g32p_row04_traceSegment_031_0945_0013, g32p_row04_traceSegment_031_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 918 27 27, g32p_row04_traceSegment_031_0918_0027, g32p_row04_traceSegment_031_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 864 54 54, g32p_row04_traceSegment_031_0864_0054, g32p_row04_traceSegment_031_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 972 13 14, g32p_row04_traceSegment_031_0972_0013, g32p_row04_traceSegment_031_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 999 13 14, g32p_row04_traceSegment_031_0999_0013, g32p_row04_traceSegment_031_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 972 27 27, g32p_row04_traceSegment_031_0972_0027, g32p_row04_traceSegment_031_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1026 13 14, g32p_row04_traceSegment_031_1026_0013, g32p_row04_traceSegment_031_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1053 13 14, g32p_row04_traceSegment_031_1053_0013, g32p_row04_traceSegment_031_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1026 27 27, g32p_row04_traceSegment_031_1026_0027, g32p_row04_traceSegment_031_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 972 54 54, g32p_row04_traceSegment_031_0972_0054, g32p_row04_traceSegment_031_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 864 108 108, g32p_row04_traceSegment_031_0864_0108, g32p_row04_traceSegment_031_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1080 13 14, g32p_row04_traceSegment_031_1080_0013, g32p_row04_traceSegment_031_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1107 13 14, g32p_row04_traceSegment_031_1107_0013, g32p_row04_traceSegment_031_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1080 27 27, g32p_row04_traceSegment_031_1080_0027, g32p_row04_traceSegment_031_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1134 13 14, g32p_row04_traceSegment_031_1134_0013, g32p_row04_traceSegment_031_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1161 13 14, g32p_row04_traceSegment_031_1161_0013, g32p_row04_traceSegment_031_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1134 27 27, g32p_row04_traceSegment_031_1134_0027, g32p_row04_traceSegment_031_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1080 54 54, g32p_row04_traceSegment_031_1080_0054, g32p_row04_traceSegment_031_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1188 13 14, g32p_row04_traceSegment_031_1188_0013, g32p_row04_traceSegment_031_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1215 13 14, g32p_row04_traceSegment_031_1215_0013, g32p_row04_traceSegment_031_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1188 27 27, g32p_row04_traceSegment_031_1188_0027, g32p_row04_traceSegment_031_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1242 13 14, g32p_row04_traceSegment_031_1242_0013, g32p_row04_traceSegment_031_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1269 13 14, g32p_row04_traceSegment_031_1269_0013, g32p_row04_traceSegment_031_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1242 27 27, g32p_row04_traceSegment_031_1242_0027, g32p_row04_traceSegment_031_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1188 54 54, g32p_row04_traceSegment_031_1188_0054, g32p_row04_traceSegment_031_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1080 108 108, g32p_row04_traceSegment_031_1080_0108, g32p_row04_traceSegment_031_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_031 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 864 216 216, g32p_row04_traceSegment_031_0864_0216, g32p_row04_traceSegment_031_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1296 13 14, g32p_row04_traceSegment_031_1296_0013, g32p_row04_traceSegment_031_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1323 13 14, g32p_row04_traceSegment_031_1323_0013, g32p_row04_traceSegment_031_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1296 27 27, g32p_row04_traceSegment_031_1296_0027, g32p_row04_traceSegment_031_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1350 13 14, g32p_row04_traceSegment_031_1350_0013, g32p_row04_traceSegment_031_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1377 13 14, g32p_row04_traceSegment_031_1377_0013, g32p_row04_traceSegment_031_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1350 27 27, g32p_row04_traceSegment_031_1350_0027, g32p_row04_traceSegment_031_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1296 54 54, g32p_row04_traceSegment_031_1296_0054, g32p_row04_traceSegment_031_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1404 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1417 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1404 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1404 13 14, g32p_row04_traceSegment_031_1404_0013, g32p_row04_traceSegment_031_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1431 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1444 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1431 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1431 13 14, g32p_row04_traceSegment_031_1431_0013, g32p_row04_traceSegment_031_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1404 54 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1404 27 27, g32p_row04_traceSegment_031_1404_0027, g32p_row04_traceSegment_031_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1471 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1458 13 14, g32p_row04_traceSegment_031_1458_0013, g32p_row04_traceSegment_031_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1485 13 14, g32p_row04_traceSegment_031_1485_0013, g32p_row04_traceSegment_031_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1458 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1458 27 27, g32p_row04_traceSegment_031_1458_0027, g32p_row04_traceSegment_031_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 1404 108 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1404 54 54, g32p_row04_traceSegment_031_1404_0054, g32p_row04_traceSegment_031_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 1296 216 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1296 108 108, g32p_row04_traceSegment_031_1296_0108, g32p_row04_traceSegment_031_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1512 13 14, g32p_row04_traceSegment_031_1512_0013, g32p_row04_traceSegment_031_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1539 13 14, g32p_row04_traceSegment_031_1539_0013, g32p_row04_traceSegment_031_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1512 27 27, g32p_row04_traceSegment_031_1512_0027, g32p_row04_traceSegment_031_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1566 13 14, g32p_row04_traceSegment_031_1566_0013, g32p_row04_traceSegment_031_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1593 13 14, g32p_row04_traceSegment_031_1593_0013, g32p_row04_traceSegment_031_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1566 27 27, g32p_row04_traceSegment_031_1566_0027, g32p_row04_traceSegment_031_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1512 54 54, g32p_row04_traceSegment_031_1512_0054, g32p_row04_traceSegment_031_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1620 13 14, g32p_row04_traceSegment_031_1620_0013, g32p_row04_traceSegment_031_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1647 13 14, g32p_row04_traceSegment_031_1647_0013, g32p_row04_traceSegment_031_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1620 27 27, g32p_row04_traceSegment_031_1620_0027, g32p_row04_traceSegment_031_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1674 13 14, g32p_row04_traceSegment_031_1674_0013, g32p_row04_traceSegment_031_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_031 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_031 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_031_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_031 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1701 13 14, g32p_row04_traceSegment_031_1701_0013, g32p_row04_traceSegment_031_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_031 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1674 27 27, g32p_row04_traceSegment_031_1674_0027, g32p_row04_traceSegment_031_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_031 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1620 54 54, g32p_row04_traceSegment_031_1620_0054, g32p_row04_traceSegment_031_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_031 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1512 108 108, g32p_row04_traceSegment_031_1512_0108, g32p_row04_traceSegment_031_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_031_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_031 1296 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 1296 216 216, g32p_row04_traceSegment_031_1296_0216, g32p_row04_traceSegment_031_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_031 864 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 864 432 432, g32p_row04_traceSegment_031_0864_0432, g32p_row04_traceSegment_031_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_031_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_031 0 1728 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_031 0 864 864, g32p_row04_traceSegment_031_0000_0864, g32p_row04_traceSegment_031_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 31 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_031_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 20) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 20) (g32p_literalTraceValue 3 20)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_020]
  decide +kernel

theorem g32p_row04_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 23) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 23) (g32p_literalTraceValue 3 23)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_023]
  decide +kernel

theorem g32p_row04_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 24) (g32p_literalTraceValue 3 24)
      [1, 1, 1] [10368] = true := by
  rw [g32p_row04_traceCoefficients_024]
  decide +kernel

theorem g32p_row04_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 25) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 25) (g32p_literalTraceValue 3 25)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_025]
  decide +kernel

theorem g32p_row04_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 27) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 27) (g32p_literalTraceValue 3 27)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_027]
  decide +kernel

theorem g32p_row04_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 28) (g32p_literalTraceValue 3 28)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_028]
  decide +kernel

theorem g32p_row04_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 29) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 29) (g32p_literalTraceValue 3 29)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_029]
  decide +kernel

theorem g32p_row04_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 31) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 31) (g32p_literalTraceValue 3 31)
      [1, 1, 1] [3456] = true := by
  rw [g32p_row04_traceCoefficients_031]
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

private def g32p_row04_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_032_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 13 14, g32p_row04_traceSegment_032_0000_0013, g32p_row04_traceSegment_032_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 27 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 40 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 27 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 27 13 14, g32p_row04_traceSegment_032_0027_0013, g32p_row04_traceSegment_032_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 0 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 27 27, g32p_row04_traceSegment_032_0000_0027, g32p_row04_traceSegment_032_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 54 13 14, g32p_row04_traceSegment_032_0054_0013, g32p_row04_traceSegment_032_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 81 13 14, g32p_row04_traceSegment_032_0081_0013, g32p_row04_traceSegment_032_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 54 27 27, g32p_row04_traceSegment_032_0054_0027, g32p_row04_traceSegment_032_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 0 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 54 54, g32p_row04_traceSegment_032_0000_0054, g32p_row04_traceSegment_032_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 108 13 14, g32p_row04_traceSegment_032_0108_0013, g32p_row04_traceSegment_032_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 135 13 14, g32p_row04_traceSegment_032_0135_0013, g32p_row04_traceSegment_032_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 108 27 27, g32p_row04_traceSegment_032_0108_0027, g32p_row04_traceSegment_032_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 162 13 14, g32p_row04_traceSegment_032_0162_0013, g32p_row04_traceSegment_032_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 189 13 14, g32p_row04_traceSegment_032_0189_0013, g32p_row04_traceSegment_032_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 162 27 27, g32p_row04_traceSegment_032_0162_0027, g32p_row04_traceSegment_032_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 108 54 54, g32p_row04_traceSegment_032_0108_0054, g32p_row04_traceSegment_032_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 108 108, g32p_row04_traceSegment_032_0000_0108, g32p_row04_traceSegment_032_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 216 13 14, g32p_row04_traceSegment_032_0216_0013, g32p_row04_traceSegment_032_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 243 13 14, g32p_row04_traceSegment_032_0243_0013, g32p_row04_traceSegment_032_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 216 27 27, g32p_row04_traceSegment_032_0216_0027, g32p_row04_traceSegment_032_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 270 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 270 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 270 13 14, g32p_row04_traceSegment_032_0270_0013, g32p_row04_traceSegment_032_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 297 13 14, g32p_row04_traceSegment_032_0297_0013, g32p_row04_traceSegment_032_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 270 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 270 27 27, g32p_row04_traceSegment_032_0270_0027, g32p_row04_traceSegment_032_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 216 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 216 54 54, g32p_row04_traceSegment_032_0216_0054, g32p_row04_traceSegment_032_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 324 13 14, g32p_row04_traceSegment_032_0324_0013, g32p_row04_traceSegment_032_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 351 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 364 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 351 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 351 13 14, g32p_row04_traceSegment_032_0351_0013, g32p_row04_traceSegment_032_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 324 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 324 27 27, g32p_row04_traceSegment_032_0324_0027, g32p_row04_traceSegment_032_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 378 13 14, g32p_row04_traceSegment_032_0378_0013, g32p_row04_traceSegment_032_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 405 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 418 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 405 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 405 13 14, g32p_row04_traceSegment_032_0405_0013, g32p_row04_traceSegment_032_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 378 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 378 27 27, g32p_row04_traceSegment_032_0378_0027, g32p_row04_traceSegment_032_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 324 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 324 54 54, g32p_row04_traceSegment_032_0324_0054, g32p_row04_traceSegment_032_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 216 216 = [6, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 216 108 108, g32p_row04_traceSegment_032_0216_0108, g32p_row04_traceSegment_032_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_032 0 432 = [8, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 216 216, g32p_row04_traceSegment_032_0000_0216, g32p_row04_traceSegment_032_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 432 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 432 13 14, g32p_row04_traceSegment_032_0432_0013, g32p_row04_traceSegment_032_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 472 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 459 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 459 13 14, g32p_row04_traceSegment_032_0459_0013, g32p_row04_traceSegment_032_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 432 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 432 27 27, g32p_row04_traceSegment_032_0432_0027, g32p_row04_traceSegment_032_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 486 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 499 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 486 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 486 13 14, g32p_row04_traceSegment_032_0486_0013, g32p_row04_traceSegment_032_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 513 13 14, g32p_row04_traceSegment_032_0513_0013, g32p_row04_traceSegment_032_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 486 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 486 27 27, g32p_row04_traceSegment_032_0486_0027, g32p_row04_traceSegment_032_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 432 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 432 54 54, g32p_row04_traceSegment_032_0432_0054, g32p_row04_traceSegment_032_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 540 13 14, g32p_row04_traceSegment_032_0540_0013, g32p_row04_traceSegment_032_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 567 13 14, g32p_row04_traceSegment_032_0567_0013, g32p_row04_traceSegment_032_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 540 27 27, g32p_row04_traceSegment_032_0540_0027, g32p_row04_traceSegment_032_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 594 13 14, g32p_row04_traceSegment_032_0594_0013, g32p_row04_traceSegment_032_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 621 13 14, g32p_row04_traceSegment_032_0621_0013, g32p_row04_traceSegment_032_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 594 27 27, g32p_row04_traceSegment_032_0594_0027, g32p_row04_traceSegment_032_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 540 54 54, g32p_row04_traceSegment_032_0540_0054, g32p_row04_traceSegment_032_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 432 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 432 108 108, g32p_row04_traceSegment_032_0432_0108, g32p_row04_traceSegment_032_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 648 13 14, g32p_row04_traceSegment_032_0648_0013, g32p_row04_traceSegment_032_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 675 13 14, g32p_row04_traceSegment_032_0675_0013, g32p_row04_traceSegment_032_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 648 27 27, g32p_row04_traceSegment_032_0648_0027, g32p_row04_traceSegment_032_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 702 13 14, g32p_row04_traceSegment_032_0702_0013, g32p_row04_traceSegment_032_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 729 13 14, g32p_row04_traceSegment_032_0729_0013, g32p_row04_traceSegment_032_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 702 27 27, g32p_row04_traceSegment_032_0702_0027, g32p_row04_traceSegment_032_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 648 54 54, g32p_row04_traceSegment_032_0648_0054, g32p_row04_traceSegment_032_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 756 13 14, g32p_row04_traceSegment_032_0756_0013, g32p_row04_traceSegment_032_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 783 13 14, g32p_row04_traceSegment_032_0783_0013, g32p_row04_traceSegment_032_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 756 27 27, g32p_row04_traceSegment_032_0756_0027, g32p_row04_traceSegment_032_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 810 13 14, g32p_row04_traceSegment_032_0810_0013, g32p_row04_traceSegment_032_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 837 13 14, g32p_row04_traceSegment_032_0837_0013, g32p_row04_traceSegment_032_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 810 27 27, g32p_row04_traceSegment_032_0810_0027, g32p_row04_traceSegment_032_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 756 54 54, g32p_row04_traceSegment_032_0756_0054, g32p_row04_traceSegment_032_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 648 108 108, g32p_row04_traceSegment_032_0648_0108, g32p_row04_traceSegment_032_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_032 432 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 432 216 216, g32p_row04_traceSegment_032_0432_0216, g32p_row04_traceSegment_032_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_032 0 864 = [12, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 432 432, g32p_row04_traceSegment_032_0000_0432, g32p_row04_traceSegment_032_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 864 13 14, g32p_row04_traceSegment_032_0864_0013, g32p_row04_traceSegment_032_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 891 13 14, g32p_row04_traceSegment_032_0891_0013, g32p_row04_traceSegment_032_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 864 27 27, g32p_row04_traceSegment_032_0864_0027, g32p_row04_traceSegment_032_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 918 13 14, g32p_row04_traceSegment_032_0918_0013, g32p_row04_traceSegment_032_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 945 13 14, g32p_row04_traceSegment_032_0945_0013, g32p_row04_traceSegment_032_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 918 27 27, g32p_row04_traceSegment_032_0918_0027, g32p_row04_traceSegment_032_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 864 54 54, g32p_row04_traceSegment_032_0864_0054, g32p_row04_traceSegment_032_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 972 13 14, g32p_row04_traceSegment_032_0972_0013, g32p_row04_traceSegment_032_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 999 13 14, g32p_row04_traceSegment_032_0999_0013, g32p_row04_traceSegment_032_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 972 27 27, g32p_row04_traceSegment_032_0972_0027, g32p_row04_traceSegment_032_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1026 13 14, g32p_row04_traceSegment_032_1026_0013, g32p_row04_traceSegment_032_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1053 13 14, g32p_row04_traceSegment_032_1053_0013, g32p_row04_traceSegment_032_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1026 27 27, g32p_row04_traceSegment_032_1026_0027, g32p_row04_traceSegment_032_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 972 54 54, g32p_row04_traceSegment_032_0972_0054, g32p_row04_traceSegment_032_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 864 108 108, g32p_row04_traceSegment_032_0864_0108, g32p_row04_traceSegment_032_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1080 13 14, g32p_row04_traceSegment_032_1080_0013, g32p_row04_traceSegment_032_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1107 13 14, g32p_row04_traceSegment_032_1107_0013, g32p_row04_traceSegment_032_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1080 27 27, g32p_row04_traceSegment_032_1080_0027, g32p_row04_traceSegment_032_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1134 13 14, g32p_row04_traceSegment_032_1134_0013, g32p_row04_traceSegment_032_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1161 13 14, g32p_row04_traceSegment_032_1161_0013, g32p_row04_traceSegment_032_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1134 27 27, g32p_row04_traceSegment_032_1134_0027, g32p_row04_traceSegment_032_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1080 54 54, g32p_row04_traceSegment_032_1080_0054, g32p_row04_traceSegment_032_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1188 13 14, g32p_row04_traceSegment_032_1188_0013, g32p_row04_traceSegment_032_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1215 13 14, g32p_row04_traceSegment_032_1215_0013, g32p_row04_traceSegment_032_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1188 27 27, g32p_row04_traceSegment_032_1188_0027, g32p_row04_traceSegment_032_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1242 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1242 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1242 13 14, g32p_row04_traceSegment_032_1242_0013, g32p_row04_traceSegment_032_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1269 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1282 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1269 27 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1269 13 14, g32p_row04_traceSegment_032_1269_0013, g32p_row04_traceSegment_032_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1242 54 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1242 27 27, g32p_row04_traceSegment_032_1242_0027, g32p_row04_traceSegment_032_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 1188 108 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1188 54 54, g32p_row04_traceSegment_032_1188_0054, g32p_row04_traceSegment_032_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 1080 216 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1080 108 108, g32p_row04_traceSegment_032_1080_0108, g32p_row04_traceSegment_032_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_032 864 432 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 864 216 216, g32p_row04_traceSegment_032_0864_0216, g32p_row04_traceSegment_032_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1309 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1296 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1296 13 14, g32p_row04_traceSegment_032_1296_0013, g32p_row04_traceSegment_032_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1323 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1336 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1323 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1323 13 14, g32p_row04_traceSegment_032_1323_0013, g32p_row04_traceSegment_032_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1296 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1296 27 27, g32p_row04_traceSegment_032_1296_0027, g32p_row04_traceSegment_032_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1350 13 14, g32p_row04_traceSegment_032_1350_0013, g32p_row04_traceSegment_032_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1377 13 14, g32p_row04_traceSegment_032_1377_0013, g32p_row04_traceSegment_032_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1350 27 27, g32p_row04_traceSegment_032_1350_0027, g32p_row04_traceSegment_032_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 1296 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1296 54 54, g32p_row04_traceSegment_032_1296_0054, g32p_row04_traceSegment_032_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1417 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1404 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1404 13 14, g32p_row04_traceSegment_032_1404_0013, g32p_row04_traceSegment_032_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1444 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1431 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1431 13 14, g32p_row04_traceSegment_032_1431_0013, g32p_row04_traceSegment_032_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1404 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1404 27 27, g32p_row04_traceSegment_032_1404_0027, g32p_row04_traceSegment_032_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1471 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1458 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1458 13 14, g32p_row04_traceSegment_032_1458_0013, g32p_row04_traceSegment_032_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1485 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1485 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1485 13 14, g32p_row04_traceSegment_032_1485_0013, g32p_row04_traceSegment_032_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1458 54 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1458 27 27, g32p_row04_traceSegment_032_1458_0027, g32p_row04_traceSegment_032_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 1404 108 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1404 54 54, g32p_row04_traceSegment_032_1404_0054, g32p_row04_traceSegment_032_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 1296 216 = [3, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1296 108 108, g32p_row04_traceSegment_032_1296_0108, g32p_row04_traceSegment_032_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1512 13 14, g32p_row04_traceSegment_032_1512_0013, g32p_row04_traceSegment_032_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1539 13 14, g32p_row04_traceSegment_032_1539_0013, g32p_row04_traceSegment_032_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1512 27 27, g32p_row04_traceSegment_032_1512_0027, g32p_row04_traceSegment_032_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1566 13 14, g32p_row04_traceSegment_032_1566_0013, g32p_row04_traceSegment_032_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1593 13 14, g32p_row04_traceSegment_032_1593_0013, g32p_row04_traceSegment_032_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1566 27 27, g32p_row04_traceSegment_032_1566_0027, g32p_row04_traceSegment_032_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1512 54 54, g32p_row04_traceSegment_032_1512_0054, g32p_row04_traceSegment_032_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1620 13 14, g32p_row04_traceSegment_032_1620_0013, g32p_row04_traceSegment_032_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1647 13 14, g32p_row04_traceSegment_032_1647_0013, g32p_row04_traceSegment_032_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1620 27 27, g32p_row04_traceSegment_032_1620_0027, g32p_row04_traceSegment_032_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1674 13 14, g32p_row04_traceSegment_032_1674_0013, g32p_row04_traceSegment_032_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_032 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_032 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_032_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_032 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1701 13 14, g32p_row04_traceSegment_032_1701_0013, g32p_row04_traceSegment_032_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_032 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1674 27 27, g32p_row04_traceSegment_032_1674_0027, g32p_row04_traceSegment_032_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_032 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1620 54 54, g32p_row04_traceSegment_032_1620_0054, g32p_row04_traceSegment_032_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_032 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1512 108 108, g32p_row04_traceSegment_032_1512_0108, g32p_row04_traceSegment_032_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_032_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_032 1296 432 = [3, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 1296 216 216, g32p_row04_traceSegment_032_1296_0216, g32p_row04_traceSegment_032_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_032 864 864 = [4, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 864 432 432, g32p_row04_traceSegment_032_0864_0432, g32p_row04_traceSegment_032_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_032_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_032 0 1728 = [16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_032 0 864 864, g32p_row04_traceSegment_032_0000_0864, g32p_row04_traceSegment_032_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 32 = [16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_032_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_034_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 0 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 13 14, g32p_row04_traceSegment_034_0000_0013, g32p_row04_traceSegment_034_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 40 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 27 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 27 13 14, g32p_row04_traceSegment_034_0027_0013, g32p_row04_traceSegment_034_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 0 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 27 27, g32p_row04_traceSegment_034_0000_0027, g32p_row04_traceSegment_034_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 54 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 54 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 54 13 14, g32p_row04_traceSegment_034_0054_0013, g32p_row04_traceSegment_034_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 81 13 14, g32p_row04_traceSegment_034_0081_0013, g32p_row04_traceSegment_034_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 54 27 27, g32p_row04_traceSegment_034_0054_0027, g32p_row04_traceSegment_034_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 0 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 54 54, g32p_row04_traceSegment_034_0000_0054, g32p_row04_traceSegment_034_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 108 13 14, g32p_row04_traceSegment_034_0108_0013, g32p_row04_traceSegment_034_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 135 13 14, g32p_row04_traceSegment_034_0135_0013, g32p_row04_traceSegment_034_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 108 27 27, g32p_row04_traceSegment_034_0108_0027, g32p_row04_traceSegment_034_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 162 13 14, g32p_row04_traceSegment_034_0162_0013, g32p_row04_traceSegment_034_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 189 13 14, g32p_row04_traceSegment_034_0189_0013, g32p_row04_traceSegment_034_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 162 27 27, g32p_row04_traceSegment_034_0162_0027, g32p_row04_traceSegment_034_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 108 54 54, g32p_row04_traceSegment_034_0108_0054, g32p_row04_traceSegment_034_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 0 216 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 108 108, g32p_row04_traceSegment_034_0000_0108, g32p_row04_traceSegment_034_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 216 13 14, g32p_row04_traceSegment_034_0216_0013, g32p_row04_traceSegment_034_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 243 13 14, g32p_row04_traceSegment_034_0243_0013, g32p_row04_traceSegment_034_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 216 27 27, g32p_row04_traceSegment_034_0216_0027, g32p_row04_traceSegment_034_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 270 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 283 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 270 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 270 13 14, g32p_row04_traceSegment_034_0270_0013, g32p_row04_traceSegment_034_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 297 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 297 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 297 13 14, g32p_row04_traceSegment_034_0297_0013, g32p_row04_traceSegment_034_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 270 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 270 27 27, g32p_row04_traceSegment_034_0270_0027, g32p_row04_traceSegment_034_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 216 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 216 54 54, g32p_row04_traceSegment_034_0216_0054, g32p_row04_traceSegment_034_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 324 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 324 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 324 13 14, g32p_row04_traceSegment_034_0324_0013, g32p_row04_traceSegment_034_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 351 13 14, g32p_row04_traceSegment_034_0351_0013, g32p_row04_traceSegment_034_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 324 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 324 27 27, g32p_row04_traceSegment_034_0324_0027, g32p_row04_traceSegment_034_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 378 13 14, g32p_row04_traceSegment_034_0378_0013, g32p_row04_traceSegment_034_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 405 13 14, g32p_row04_traceSegment_034_0405_0013, g32p_row04_traceSegment_034_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 378 27 27, g32p_row04_traceSegment_034_0378_0027, g32p_row04_traceSegment_034_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 324 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 324 54 54, g32p_row04_traceSegment_034_0324_0054, g32p_row04_traceSegment_034_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 216 216 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 216 108 108, g32p_row04_traceSegment_034_0216_0108, g32p_row04_traceSegment_034_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_034 0 432 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 216 216, g32p_row04_traceSegment_034_0000_0216, g32p_row04_traceSegment_034_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 432 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 445 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 432 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 432 13 14, g32p_row04_traceSegment_034_0432_0013, g32p_row04_traceSegment_034_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 459 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 459 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 459 13 14, g32p_row04_traceSegment_034_0459_0013, g32p_row04_traceSegment_034_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 432 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 432 27 27, g32p_row04_traceSegment_034_0432_0027, g32p_row04_traceSegment_034_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 486 13 14, g32p_row04_traceSegment_034_0486_0013, g32p_row04_traceSegment_034_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 513 13 14, g32p_row04_traceSegment_034_0513_0013, g32p_row04_traceSegment_034_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 486 27 27, g32p_row04_traceSegment_034_0486_0027, g32p_row04_traceSegment_034_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 432 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 432 54 54, g32p_row04_traceSegment_034_0432_0054, g32p_row04_traceSegment_034_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 540 13 14, g32p_row04_traceSegment_034_0540_0013, g32p_row04_traceSegment_034_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 567 13 14, g32p_row04_traceSegment_034_0567_0013, g32p_row04_traceSegment_034_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 540 27 27, g32p_row04_traceSegment_034_0540_0027, g32p_row04_traceSegment_034_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 594 13 14, g32p_row04_traceSegment_034_0594_0013, g32p_row04_traceSegment_034_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 621 13 14, g32p_row04_traceSegment_034_0621_0013, g32p_row04_traceSegment_034_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 594 27 27, g32p_row04_traceSegment_034_0594_0027, g32p_row04_traceSegment_034_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 540 54 54, g32p_row04_traceSegment_034_0540_0054, g32p_row04_traceSegment_034_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 432 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 432 108 108, g32p_row04_traceSegment_034_0432_0108, g32p_row04_traceSegment_034_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 648 13 14, g32p_row04_traceSegment_034_0648_0013, g32p_row04_traceSegment_034_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 675 13 14, g32p_row04_traceSegment_034_0675_0013, g32p_row04_traceSegment_034_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 648 27 27, g32p_row04_traceSegment_034_0648_0027, g32p_row04_traceSegment_034_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 702 13 14, g32p_row04_traceSegment_034_0702_0013, g32p_row04_traceSegment_034_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 729 13 14, g32p_row04_traceSegment_034_0729_0013, g32p_row04_traceSegment_034_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 702 27 27, g32p_row04_traceSegment_034_0702_0027, g32p_row04_traceSegment_034_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 648 54 54, g32p_row04_traceSegment_034_0648_0054, g32p_row04_traceSegment_034_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 756 13 14, g32p_row04_traceSegment_034_0756_0013, g32p_row04_traceSegment_034_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 783 13 14, g32p_row04_traceSegment_034_0783_0013, g32p_row04_traceSegment_034_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 756 27 27, g32p_row04_traceSegment_034_0756_0027, g32p_row04_traceSegment_034_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 810 13 14, g32p_row04_traceSegment_034_0810_0013, g32p_row04_traceSegment_034_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 837 13 14, g32p_row04_traceSegment_034_0837_0013, g32p_row04_traceSegment_034_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 810 27 27, g32p_row04_traceSegment_034_0810_0027, g32p_row04_traceSegment_034_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 756 54 54, g32p_row04_traceSegment_034_0756_0054, g32p_row04_traceSegment_034_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 648 108 108, g32p_row04_traceSegment_034_0648_0108, g32p_row04_traceSegment_034_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_034 432 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 432 216 216, g32p_row04_traceSegment_034_0432_0216, g32p_row04_traceSegment_034_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_034 0 864 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 432 432, g32p_row04_traceSegment_034_0000_0432, g32p_row04_traceSegment_034_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 864 13 14, g32p_row04_traceSegment_034_0864_0013, g32p_row04_traceSegment_034_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 891 13 14, g32p_row04_traceSegment_034_0891_0013, g32p_row04_traceSegment_034_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 864 27 27, g32p_row04_traceSegment_034_0864_0027, g32p_row04_traceSegment_034_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 918 13 14, g32p_row04_traceSegment_034_0918_0013, g32p_row04_traceSegment_034_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 945 13 14, g32p_row04_traceSegment_034_0945_0013, g32p_row04_traceSegment_034_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 918 27 27, g32p_row04_traceSegment_034_0918_0027, g32p_row04_traceSegment_034_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 864 54 54, g32p_row04_traceSegment_034_0864_0054, g32p_row04_traceSegment_034_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 972 13 14, g32p_row04_traceSegment_034_0972_0013, g32p_row04_traceSegment_034_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 999 13 14, g32p_row04_traceSegment_034_0999_0013, g32p_row04_traceSegment_034_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 972 27 27, g32p_row04_traceSegment_034_0972_0027, g32p_row04_traceSegment_034_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1026 13 14, g32p_row04_traceSegment_034_1026_0013, g32p_row04_traceSegment_034_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1053 13 14, g32p_row04_traceSegment_034_1053_0013, g32p_row04_traceSegment_034_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1026 27 27, g32p_row04_traceSegment_034_1026_0027, g32p_row04_traceSegment_034_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 972 54 54, g32p_row04_traceSegment_034_0972_0054, g32p_row04_traceSegment_034_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 864 108 108, g32p_row04_traceSegment_034_0864_0108, g32p_row04_traceSegment_034_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1080 13 14, g32p_row04_traceSegment_034_1080_0013, g32p_row04_traceSegment_034_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1107 13 14, g32p_row04_traceSegment_034_1107_0013, g32p_row04_traceSegment_034_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1080 27 27, g32p_row04_traceSegment_034_1080_0027, g32p_row04_traceSegment_034_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1134 13 14, g32p_row04_traceSegment_034_1134_0013, g32p_row04_traceSegment_034_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1161 13 14, g32p_row04_traceSegment_034_1161_0013, g32p_row04_traceSegment_034_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1134 27 27, g32p_row04_traceSegment_034_1134_0027, g32p_row04_traceSegment_034_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1080 54 54, g32p_row04_traceSegment_034_1080_0054, g32p_row04_traceSegment_034_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1188 13 14, g32p_row04_traceSegment_034_1188_0013, g32p_row04_traceSegment_034_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1215 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1215 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1215 13 14, g32p_row04_traceSegment_034_1215_0013, g32p_row04_traceSegment_034_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1188 27 27, g32p_row04_traceSegment_034_1188_0027, g32p_row04_traceSegment_034_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1242 13 14, g32p_row04_traceSegment_034_1242_0013, g32p_row04_traceSegment_034_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1269 13 14, g32p_row04_traceSegment_034_1269_0013, g32p_row04_traceSegment_034_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1242 27 27, g32p_row04_traceSegment_034_1242_0027, g32p_row04_traceSegment_034_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 1188 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1188 54 54, g32p_row04_traceSegment_034_1188_0054, g32p_row04_traceSegment_034_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1080 108 108, g32p_row04_traceSegment_034_1080_0108, g32p_row04_traceSegment_034_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_034 864 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 864 216 216, g32p_row04_traceSegment_034_0864_0216, g32p_row04_traceSegment_034_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1296 13 14, g32p_row04_traceSegment_034_1296_0013, g32p_row04_traceSegment_034_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1336 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1323 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1323 13 14, g32p_row04_traceSegment_034_1323_0013, g32p_row04_traceSegment_034_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1296 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1296 27 27, g32p_row04_traceSegment_034_1296_0027, g32p_row04_traceSegment_034_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1350 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1363 14 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1350 27 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1350 13 14, g32p_row04_traceSegment_034_1350_0013, g32p_row04_traceSegment_034_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1377 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1390 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1377 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1377 13 14, g32p_row04_traceSegment_034_1377_0013, g32p_row04_traceSegment_034_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1350 54 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1350 27 27, g32p_row04_traceSegment_034_1350_0027, g32p_row04_traceSegment_034_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 1296 108 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1296 54 54, g32p_row04_traceSegment_034_1296_0054, g32p_row04_traceSegment_034_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1404 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1404 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1404 13 14, g32p_row04_traceSegment_034_1404_0013, g32p_row04_traceSegment_034_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1444 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1431 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1431 13 14, g32p_row04_traceSegment_034_1431_0013, g32p_row04_traceSegment_034_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1404 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1404 27 27, g32p_row04_traceSegment_034_1404_0027, g32p_row04_traceSegment_034_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1458 13 14, g32p_row04_traceSegment_034_1458_0013, g32p_row04_traceSegment_034_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1485 13 14, g32p_row04_traceSegment_034_1485_0013, g32p_row04_traceSegment_034_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1458 27 27, g32p_row04_traceSegment_034_1458_0027, g32p_row04_traceSegment_034_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 1404 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1404 54 54, g32p_row04_traceSegment_034_1404_0054, g32p_row04_traceSegment_034_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 1296 216 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1296 108 108, g32p_row04_traceSegment_034_1296_0108, g32p_row04_traceSegment_034_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1512 13 14, g32p_row04_traceSegment_034_1512_0013, g32p_row04_traceSegment_034_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1539 13 14, g32p_row04_traceSegment_034_1539_0013, g32p_row04_traceSegment_034_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1512 27 27, g32p_row04_traceSegment_034_1512_0027, g32p_row04_traceSegment_034_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1566 13 14, g32p_row04_traceSegment_034_1566_0013, g32p_row04_traceSegment_034_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1593 13 14, g32p_row04_traceSegment_034_1593_0013, g32p_row04_traceSegment_034_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1566 27 27, g32p_row04_traceSegment_034_1566_0027, g32p_row04_traceSegment_034_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1512 54 54, g32p_row04_traceSegment_034_1512_0054, g32p_row04_traceSegment_034_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1620 13 14, g32p_row04_traceSegment_034_1620_0013, g32p_row04_traceSegment_034_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1647 13 14, g32p_row04_traceSegment_034_1647_0013, g32p_row04_traceSegment_034_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1620 27 27, g32p_row04_traceSegment_034_1620_0027, g32p_row04_traceSegment_034_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1674 13 14, g32p_row04_traceSegment_034_1674_0013, g32p_row04_traceSegment_034_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_034 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_034 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_034_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_034 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1701 13 14, g32p_row04_traceSegment_034_1701_0013, g32p_row04_traceSegment_034_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_034 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1674 27 27, g32p_row04_traceSegment_034_1674_0027, g32p_row04_traceSegment_034_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_034 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1620 54 54, g32p_row04_traceSegment_034_1620_0054, g32p_row04_traceSegment_034_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_034 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1512 108 108, g32p_row04_traceSegment_034_1512_0108, g32p_row04_traceSegment_034_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_034_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_034 1296 432 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 1296 216 216, g32p_row04_traceSegment_034_1296_0216, g32p_row04_traceSegment_034_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_034 864 864 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 864 432 432, g32p_row04_traceSegment_034_0864_0432, g32p_row04_traceSegment_034_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_034_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_034 0 1728 = [0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_034 0 864 864, g32p_row04_traceSegment_034_0000_0864, g32p_row04_traceSegment_034_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 34 = [0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_034_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_035_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 0 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 0 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 13 14, g32p_row04_traceSegment_035_0000_0013, g32p_row04_traceSegment_035_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 40 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 27 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 27 13 14, g32p_row04_traceSegment_035_0027_0013, g32p_row04_traceSegment_035_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 0 54 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 27 27, g32p_row04_traceSegment_035_0000_0027, g32p_row04_traceSegment_035_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 54 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 54 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 54 13 14, g32p_row04_traceSegment_035_0054_0013, g32p_row04_traceSegment_035_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 81 13 14, g32p_row04_traceSegment_035_0081_0013, g32p_row04_traceSegment_035_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 54 27 27, g32p_row04_traceSegment_035_0054_0027, g32p_row04_traceSegment_035_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 0 108 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 54 54, g32p_row04_traceSegment_035_0000_0054, g32p_row04_traceSegment_035_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 108 13 14, g32p_row04_traceSegment_035_0108_0013, g32p_row04_traceSegment_035_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 135 13 14, g32p_row04_traceSegment_035_0135_0013, g32p_row04_traceSegment_035_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 108 27 27, g32p_row04_traceSegment_035_0108_0027, g32p_row04_traceSegment_035_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 162 13 14, g32p_row04_traceSegment_035_0162_0013, g32p_row04_traceSegment_035_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 189 13 14, g32p_row04_traceSegment_035_0189_0013, g32p_row04_traceSegment_035_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 162 27 27, g32p_row04_traceSegment_035_0162_0027, g32p_row04_traceSegment_035_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 108 54 54, g32p_row04_traceSegment_035_0108_0054, g32p_row04_traceSegment_035_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 0 216 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 108 108, g32p_row04_traceSegment_035_0000_0108, g32p_row04_traceSegment_035_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 216 13 14, g32p_row04_traceSegment_035_0216_0013, g32p_row04_traceSegment_035_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 243 13 14, g32p_row04_traceSegment_035_0243_0013, g32p_row04_traceSegment_035_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 216 27 27, g32p_row04_traceSegment_035_0216_0027, g32p_row04_traceSegment_035_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 270 13 14, g32p_row04_traceSegment_035_0270_0013, g32p_row04_traceSegment_035_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 297 13 14, g32p_row04_traceSegment_035_0297_0013, g32p_row04_traceSegment_035_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 270 27 27, g32p_row04_traceSegment_035_0270_0027, g32p_row04_traceSegment_035_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 216 54 54, g32p_row04_traceSegment_035_0216_0054, g32p_row04_traceSegment_035_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 337 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 324 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 324 13 14, g32p_row04_traceSegment_035_0324_0013, g32p_row04_traceSegment_035_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 351 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 351 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 351 13 14, g32p_row04_traceSegment_035_0351_0013, g32p_row04_traceSegment_035_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 324 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 324 27 27, g32p_row04_traceSegment_035_0324_0027, g32p_row04_traceSegment_035_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 378 13 14, g32p_row04_traceSegment_035_0378_0013, g32p_row04_traceSegment_035_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 405 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 418 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 405 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 405 13 14, g32p_row04_traceSegment_035_0405_0013, g32p_row04_traceSegment_035_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 378 54 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 378 27 27, g32p_row04_traceSegment_035_0378_0027, g32p_row04_traceSegment_035_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 324 108 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 324 54 54, g32p_row04_traceSegment_035_0324_0054, g32p_row04_traceSegment_035_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 216 216 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 216 108 108, g32p_row04_traceSegment_035_0216_0108, g32p_row04_traceSegment_035_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_035 0 432 = [3, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 216 216, g32p_row04_traceSegment_035_0000_0216, g32p_row04_traceSegment_035_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 432 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 445 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 432 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 432 13 14, g32p_row04_traceSegment_035_0432_0013, g32p_row04_traceSegment_035_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 459 13 14, g32p_row04_traceSegment_035_0459_0013, g32p_row04_traceSegment_035_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 432 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 432 27 27, g32p_row04_traceSegment_035_0432_0027, g32p_row04_traceSegment_035_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 499 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 486 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 486 13 14, g32p_row04_traceSegment_035_0486_0013, g32p_row04_traceSegment_035_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 513 13 14, g32p_row04_traceSegment_035_0513_0013, g32p_row04_traceSegment_035_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 486 27 27, g32p_row04_traceSegment_035_0486_0027, g32p_row04_traceSegment_035_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 432 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 432 54 54, g32p_row04_traceSegment_035_0432_0054, g32p_row04_traceSegment_035_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 540 13 14, g32p_row04_traceSegment_035_0540_0013, g32p_row04_traceSegment_035_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 567 13 14, g32p_row04_traceSegment_035_0567_0013, g32p_row04_traceSegment_035_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 540 27 27, g32p_row04_traceSegment_035_0540_0027, g32p_row04_traceSegment_035_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 594 13 14, g32p_row04_traceSegment_035_0594_0013, g32p_row04_traceSegment_035_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 621 13 14, g32p_row04_traceSegment_035_0621_0013, g32p_row04_traceSegment_035_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 594 27 27, g32p_row04_traceSegment_035_0594_0027, g32p_row04_traceSegment_035_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 540 54 54, g32p_row04_traceSegment_035_0540_0054, g32p_row04_traceSegment_035_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 432 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 432 108 108, g32p_row04_traceSegment_035_0432_0108, g32p_row04_traceSegment_035_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 648 13 14, g32p_row04_traceSegment_035_0648_0013, g32p_row04_traceSegment_035_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 675 13 14, g32p_row04_traceSegment_035_0675_0013, g32p_row04_traceSegment_035_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 648 27 27, g32p_row04_traceSegment_035_0648_0027, g32p_row04_traceSegment_035_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 702 13 14, g32p_row04_traceSegment_035_0702_0013, g32p_row04_traceSegment_035_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 729 13 14, g32p_row04_traceSegment_035_0729_0013, g32p_row04_traceSegment_035_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 702 27 27, g32p_row04_traceSegment_035_0702_0027, g32p_row04_traceSegment_035_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 648 54 54, g32p_row04_traceSegment_035_0648_0054, g32p_row04_traceSegment_035_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 756 13 14, g32p_row04_traceSegment_035_0756_0013, g32p_row04_traceSegment_035_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 783 13 14, g32p_row04_traceSegment_035_0783_0013, g32p_row04_traceSegment_035_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 756 27 27, g32p_row04_traceSegment_035_0756_0027, g32p_row04_traceSegment_035_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 810 13 14, g32p_row04_traceSegment_035_0810_0013, g32p_row04_traceSegment_035_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 837 13 14, g32p_row04_traceSegment_035_0837_0013, g32p_row04_traceSegment_035_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 810 27 27, g32p_row04_traceSegment_035_0810_0027, g32p_row04_traceSegment_035_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 756 54 54, g32p_row04_traceSegment_035_0756_0054, g32p_row04_traceSegment_035_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 648 108 108, g32p_row04_traceSegment_035_0648_0108, g32p_row04_traceSegment_035_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_035 432 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 432 216 216, g32p_row04_traceSegment_035_0432_0216, g32p_row04_traceSegment_035_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_035 0 864 = [7, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 432 432, g32p_row04_traceSegment_035_0000_0432, g32p_row04_traceSegment_035_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 864 13 14, g32p_row04_traceSegment_035_0864_0013, g32p_row04_traceSegment_035_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 891 13 14, g32p_row04_traceSegment_035_0891_0013, g32p_row04_traceSegment_035_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 864 27 27, g32p_row04_traceSegment_035_0864_0027, g32p_row04_traceSegment_035_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 918 13 14, g32p_row04_traceSegment_035_0918_0013, g32p_row04_traceSegment_035_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 945 13 14, g32p_row04_traceSegment_035_0945_0013, g32p_row04_traceSegment_035_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 918 27 27, g32p_row04_traceSegment_035_0918_0027, g32p_row04_traceSegment_035_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 864 54 54, g32p_row04_traceSegment_035_0864_0054, g32p_row04_traceSegment_035_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 972 13 14, g32p_row04_traceSegment_035_0972_0013, g32p_row04_traceSegment_035_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 999 13 14, g32p_row04_traceSegment_035_0999_0013, g32p_row04_traceSegment_035_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 972 27 27, g32p_row04_traceSegment_035_0972_0027, g32p_row04_traceSegment_035_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1026 13 14, g32p_row04_traceSegment_035_1026_0013, g32p_row04_traceSegment_035_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1053 13 14, g32p_row04_traceSegment_035_1053_0013, g32p_row04_traceSegment_035_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1026 27 27, g32p_row04_traceSegment_035_1026_0027, g32p_row04_traceSegment_035_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 972 54 54, g32p_row04_traceSegment_035_0972_0054, g32p_row04_traceSegment_035_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 864 108 108, g32p_row04_traceSegment_035_0864_0108, g32p_row04_traceSegment_035_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1080 13 14, g32p_row04_traceSegment_035_1080_0013, g32p_row04_traceSegment_035_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1107 13 14, g32p_row04_traceSegment_035_1107_0013, g32p_row04_traceSegment_035_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1080 27 27, g32p_row04_traceSegment_035_1080_0027, g32p_row04_traceSegment_035_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1134 13 14, g32p_row04_traceSegment_035_1134_0013, g32p_row04_traceSegment_035_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1161 13 14, g32p_row04_traceSegment_035_1161_0013, g32p_row04_traceSegment_035_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1134 27 27, g32p_row04_traceSegment_035_1134_0027, g32p_row04_traceSegment_035_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1080 54 54, g32p_row04_traceSegment_035_1080_0054, g32p_row04_traceSegment_035_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1201 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1188 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1188 13 14, g32p_row04_traceSegment_035_1188_0013, g32p_row04_traceSegment_035_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1215 13 14, g32p_row04_traceSegment_035_1215_0013, g32p_row04_traceSegment_035_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1188 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1188 27 27, g32p_row04_traceSegment_035_1188_0027, g32p_row04_traceSegment_035_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1242 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1242 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1242 13 14, g32p_row04_traceSegment_035_1242_0013, g32p_row04_traceSegment_035_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1269 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1282 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1269 27 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1269 13 14, g32p_row04_traceSegment_035_1269_0013, g32p_row04_traceSegment_035_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1242 54 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1242 27 27, g32p_row04_traceSegment_035_1242_0027, g32p_row04_traceSegment_035_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 1188 108 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1188 54 54, g32p_row04_traceSegment_035_1188_0054, g32p_row04_traceSegment_035_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 1080 216 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1080 108 108, g32p_row04_traceSegment_035_1080_0108, g32p_row04_traceSegment_035_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_035 864 432 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 864 216 216, g32p_row04_traceSegment_035_0864_0216, g32p_row04_traceSegment_035_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1296 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1309 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1296 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1296 13 14, g32p_row04_traceSegment_035_1296_0013, g32p_row04_traceSegment_035_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1323 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1336 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1323 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1323 13 14, g32p_row04_traceSegment_035_1323_0013, g32p_row04_traceSegment_035_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1296 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1296 27 27, g32p_row04_traceSegment_035_1296_0027, g32p_row04_traceSegment_035_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1350 13 14, g32p_row04_traceSegment_035_1350_0013, g32p_row04_traceSegment_035_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1377 13 14, g32p_row04_traceSegment_035_1377_0013, g32p_row04_traceSegment_035_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1350 27 27, g32p_row04_traceSegment_035_1350_0027, g32p_row04_traceSegment_035_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 1296 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1296 54 54, g32p_row04_traceSegment_035_1296_0054, g32p_row04_traceSegment_035_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1404 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1404 13 14, g32p_row04_traceSegment_035_1404_0013, g32p_row04_traceSegment_035_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1431 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1431 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1431 13 14, g32p_row04_traceSegment_035_1431_0013, g32p_row04_traceSegment_035_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1404 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1404 27 27, g32p_row04_traceSegment_035_1404_0027, g32p_row04_traceSegment_035_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1458 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1471 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1458 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1458 13 14, g32p_row04_traceSegment_035_1458_0013, g32p_row04_traceSegment_035_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1485 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1498 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1485 27 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1485 13 14, g32p_row04_traceSegment_035_1485_0013, g32p_row04_traceSegment_035_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1458 54 = [2, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1458 27 27, g32p_row04_traceSegment_035_1458_0027, g32p_row04_traceSegment_035_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 1404 108 = [2, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1404 54 54, g32p_row04_traceSegment_035_1404_0054, g32p_row04_traceSegment_035_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 1296 216 = [6, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1296 108 108, g32p_row04_traceSegment_035_1296_0108, g32p_row04_traceSegment_035_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1512 13 14, g32p_row04_traceSegment_035_1512_0013, g32p_row04_traceSegment_035_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1539 13 14, g32p_row04_traceSegment_035_1539_0013, g32p_row04_traceSegment_035_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1512 27 27, g32p_row04_traceSegment_035_1512_0027, g32p_row04_traceSegment_035_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1566 13 14, g32p_row04_traceSegment_035_1566_0013, g32p_row04_traceSegment_035_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1593 13 14, g32p_row04_traceSegment_035_1593_0013, g32p_row04_traceSegment_035_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1566 27 27, g32p_row04_traceSegment_035_1566_0027, g32p_row04_traceSegment_035_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1512 54 54, g32p_row04_traceSegment_035_1512_0054, g32p_row04_traceSegment_035_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1620 13 14, g32p_row04_traceSegment_035_1620_0013, g32p_row04_traceSegment_035_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1647 13 14, g32p_row04_traceSegment_035_1647_0013, g32p_row04_traceSegment_035_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1620 27 27, g32p_row04_traceSegment_035_1620_0027, g32p_row04_traceSegment_035_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1674 13 14, g32p_row04_traceSegment_035_1674_0013, g32p_row04_traceSegment_035_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_035 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_035 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_035_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_035 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1701 13 14, g32p_row04_traceSegment_035_1701_0013, g32p_row04_traceSegment_035_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_035 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1674 27 27, g32p_row04_traceSegment_035_1674_0027, g32p_row04_traceSegment_035_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_035 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1620 54 54, g32p_row04_traceSegment_035_1620_0054, g32p_row04_traceSegment_035_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_035 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1512 108 108, g32p_row04_traceSegment_035_1512_0108, g32p_row04_traceSegment_035_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_035_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_035 1296 432 = [6, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 1296 216 216, g32p_row04_traceSegment_035_1296_0216, g32p_row04_traceSegment_035_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_035 864 864 = [9, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 864 432 432, g32p_row04_traceSegment_035_0864_0432, g32p_row04_traceSegment_035_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_035_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_035 0 1728 = [16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_035 0 864 864, g32p_row04_traceSegment_035_0000_0864, g32p_row04_traceSegment_035_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 35 = [16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_035_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_037_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 13 14, g32p_row04_traceSegment_037_0000_0013, g32p_row04_traceSegment_037_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 27 13 14, g32p_row04_traceSegment_037_0027_0013, g32p_row04_traceSegment_037_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 27 27, g32p_row04_traceSegment_037_0000_0027, g32p_row04_traceSegment_037_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 54 13 14, g32p_row04_traceSegment_037_0054_0013, g32p_row04_traceSegment_037_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 81 13 14, g32p_row04_traceSegment_037_0081_0013, g32p_row04_traceSegment_037_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 54 27 27, g32p_row04_traceSegment_037_0054_0027, g32p_row04_traceSegment_037_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 54 54, g32p_row04_traceSegment_037_0000_0054, g32p_row04_traceSegment_037_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 108 13 14, g32p_row04_traceSegment_037_0108_0013, g32p_row04_traceSegment_037_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 135 13 14, g32p_row04_traceSegment_037_0135_0013, g32p_row04_traceSegment_037_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 108 27 27, g32p_row04_traceSegment_037_0108_0027, g32p_row04_traceSegment_037_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 162 13 14, g32p_row04_traceSegment_037_0162_0013, g32p_row04_traceSegment_037_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 189 13 14, g32p_row04_traceSegment_037_0189_0013, g32p_row04_traceSegment_037_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 162 27 27, g32p_row04_traceSegment_037_0162_0027, g32p_row04_traceSegment_037_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 108 54 54, g32p_row04_traceSegment_037_0108_0054, g32p_row04_traceSegment_037_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 108 108, g32p_row04_traceSegment_037_0000_0108, g32p_row04_traceSegment_037_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 216 13 14, g32p_row04_traceSegment_037_0216_0013, g32p_row04_traceSegment_037_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 243 13 14, g32p_row04_traceSegment_037_0243_0013, g32p_row04_traceSegment_037_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 216 27 27, g32p_row04_traceSegment_037_0216_0027, g32p_row04_traceSegment_037_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 270 13 14, g32p_row04_traceSegment_037_0270_0013, g32p_row04_traceSegment_037_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 297 13 14, g32p_row04_traceSegment_037_0297_0013, g32p_row04_traceSegment_037_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 270 27 27, g32p_row04_traceSegment_037_0270_0027, g32p_row04_traceSegment_037_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 216 54 54, g32p_row04_traceSegment_037_0216_0054, g32p_row04_traceSegment_037_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 324 13 14, g32p_row04_traceSegment_037_0324_0013, g32p_row04_traceSegment_037_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 351 13 14, g32p_row04_traceSegment_037_0351_0013, g32p_row04_traceSegment_037_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 324 27 27, g32p_row04_traceSegment_037_0324_0027, g32p_row04_traceSegment_037_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 378 13 14, g32p_row04_traceSegment_037_0378_0013, g32p_row04_traceSegment_037_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 405 13 14, g32p_row04_traceSegment_037_0405_0013, g32p_row04_traceSegment_037_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 378 27 27, g32p_row04_traceSegment_037_0378_0027, g32p_row04_traceSegment_037_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 324 54 54, g32p_row04_traceSegment_037_0324_0054, g32p_row04_traceSegment_037_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 216 108 108, g32p_row04_traceSegment_037_0216_0108, g32p_row04_traceSegment_037_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_037 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 216 216, g32p_row04_traceSegment_037_0000_0216, g32p_row04_traceSegment_037_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 432 13 14, g32p_row04_traceSegment_037_0432_0013, g32p_row04_traceSegment_037_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 459 13 14, g32p_row04_traceSegment_037_0459_0013, g32p_row04_traceSegment_037_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 432 27 27, g32p_row04_traceSegment_037_0432_0027, g32p_row04_traceSegment_037_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 486 13 14, g32p_row04_traceSegment_037_0486_0013, g32p_row04_traceSegment_037_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 513 13 14, g32p_row04_traceSegment_037_0513_0013, g32p_row04_traceSegment_037_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 486 27 27, g32p_row04_traceSegment_037_0486_0027, g32p_row04_traceSegment_037_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 432 54 54, g32p_row04_traceSegment_037_0432_0054, g32p_row04_traceSegment_037_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 540 13 14, g32p_row04_traceSegment_037_0540_0013, g32p_row04_traceSegment_037_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 567 13 14, g32p_row04_traceSegment_037_0567_0013, g32p_row04_traceSegment_037_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 540 27 27, g32p_row04_traceSegment_037_0540_0027, g32p_row04_traceSegment_037_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 594 13 14, g32p_row04_traceSegment_037_0594_0013, g32p_row04_traceSegment_037_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 621 13 14, g32p_row04_traceSegment_037_0621_0013, g32p_row04_traceSegment_037_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 594 27 27, g32p_row04_traceSegment_037_0594_0027, g32p_row04_traceSegment_037_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 540 54 54, g32p_row04_traceSegment_037_0540_0054, g32p_row04_traceSegment_037_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 432 108 108, g32p_row04_traceSegment_037_0432_0108, g32p_row04_traceSegment_037_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 648 13 14, g32p_row04_traceSegment_037_0648_0013, g32p_row04_traceSegment_037_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 675 13 14, g32p_row04_traceSegment_037_0675_0013, g32p_row04_traceSegment_037_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 648 27 27, g32p_row04_traceSegment_037_0648_0027, g32p_row04_traceSegment_037_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 702 13 14, g32p_row04_traceSegment_037_0702_0013, g32p_row04_traceSegment_037_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 729 13 14, g32p_row04_traceSegment_037_0729_0013, g32p_row04_traceSegment_037_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 702 27 27, g32p_row04_traceSegment_037_0702_0027, g32p_row04_traceSegment_037_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 648 54 54, g32p_row04_traceSegment_037_0648_0054, g32p_row04_traceSegment_037_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 756 13 14, g32p_row04_traceSegment_037_0756_0013, g32p_row04_traceSegment_037_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 783 13 14, g32p_row04_traceSegment_037_0783_0013, g32p_row04_traceSegment_037_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 756 27 27, g32p_row04_traceSegment_037_0756_0027, g32p_row04_traceSegment_037_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 810 13 14, g32p_row04_traceSegment_037_0810_0013, g32p_row04_traceSegment_037_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 837 13 14, g32p_row04_traceSegment_037_0837_0013, g32p_row04_traceSegment_037_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 810 27 27, g32p_row04_traceSegment_037_0810_0027, g32p_row04_traceSegment_037_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 756 54 54, g32p_row04_traceSegment_037_0756_0054, g32p_row04_traceSegment_037_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 648 108 108, g32p_row04_traceSegment_037_0648_0108, g32p_row04_traceSegment_037_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_037 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 432 216 216, g32p_row04_traceSegment_037_0432_0216, g32p_row04_traceSegment_037_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_037 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 432 432, g32p_row04_traceSegment_037_0000_0432, g32p_row04_traceSegment_037_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 864 13 14, g32p_row04_traceSegment_037_0864_0013, g32p_row04_traceSegment_037_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 891 13 14, g32p_row04_traceSegment_037_0891_0013, g32p_row04_traceSegment_037_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 864 27 27, g32p_row04_traceSegment_037_0864_0027, g32p_row04_traceSegment_037_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 918 13 14, g32p_row04_traceSegment_037_0918_0013, g32p_row04_traceSegment_037_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 945 13 14, g32p_row04_traceSegment_037_0945_0013, g32p_row04_traceSegment_037_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 918 27 27, g32p_row04_traceSegment_037_0918_0027, g32p_row04_traceSegment_037_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 864 54 54, g32p_row04_traceSegment_037_0864_0054, g32p_row04_traceSegment_037_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 972 13 14, g32p_row04_traceSegment_037_0972_0013, g32p_row04_traceSegment_037_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 999 13 14, g32p_row04_traceSegment_037_0999_0013, g32p_row04_traceSegment_037_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 972 27 27, g32p_row04_traceSegment_037_0972_0027, g32p_row04_traceSegment_037_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1026 13 14, g32p_row04_traceSegment_037_1026_0013, g32p_row04_traceSegment_037_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1053 13 14, g32p_row04_traceSegment_037_1053_0013, g32p_row04_traceSegment_037_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1026 27 27, g32p_row04_traceSegment_037_1026_0027, g32p_row04_traceSegment_037_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 972 54 54, g32p_row04_traceSegment_037_0972_0054, g32p_row04_traceSegment_037_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 864 108 108, g32p_row04_traceSegment_037_0864_0108, g32p_row04_traceSegment_037_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1080 13 14, g32p_row04_traceSegment_037_1080_0013, g32p_row04_traceSegment_037_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1107 13 14, g32p_row04_traceSegment_037_1107_0013, g32p_row04_traceSegment_037_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1080 27 27, g32p_row04_traceSegment_037_1080_0027, g32p_row04_traceSegment_037_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1134 13 14, g32p_row04_traceSegment_037_1134_0013, g32p_row04_traceSegment_037_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1161 13 14, g32p_row04_traceSegment_037_1161_0013, g32p_row04_traceSegment_037_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1134 27 27, g32p_row04_traceSegment_037_1134_0027, g32p_row04_traceSegment_037_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1080 54 54, g32p_row04_traceSegment_037_1080_0054, g32p_row04_traceSegment_037_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1188 13 14, g32p_row04_traceSegment_037_1188_0013, g32p_row04_traceSegment_037_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1215 13 14, g32p_row04_traceSegment_037_1215_0013, g32p_row04_traceSegment_037_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1188 27 27, g32p_row04_traceSegment_037_1188_0027, g32p_row04_traceSegment_037_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1242 13 14, g32p_row04_traceSegment_037_1242_0013, g32p_row04_traceSegment_037_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1269 13 14, g32p_row04_traceSegment_037_1269_0013, g32p_row04_traceSegment_037_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1242 27 27, g32p_row04_traceSegment_037_1242_0027, g32p_row04_traceSegment_037_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1188 54 54, g32p_row04_traceSegment_037_1188_0054, g32p_row04_traceSegment_037_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1080 108 108, g32p_row04_traceSegment_037_1080_0108, g32p_row04_traceSegment_037_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_037 864 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 864 216 216, g32p_row04_traceSegment_037_0864_0216, g32p_row04_traceSegment_037_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1296 13 14, g32p_row04_traceSegment_037_1296_0013, g32p_row04_traceSegment_037_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1323 13 14, g32p_row04_traceSegment_037_1323_0013, g32p_row04_traceSegment_037_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1296 27 27, g32p_row04_traceSegment_037_1296_0027, g32p_row04_traceSegment_037_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1350 13 14, g32p_row04_traceSegment_037_1350_0013, g32p_row04_traceSegment_037_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1377 13 14, g32p_row04_traceSegment_037_1377_0013, g32p_row04_traceSegment_037_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1350 27 27, g32p_row04_traceSegment_037_1350_0027, g32p_row04_traceSegment_037_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1296 54 54, g32p_row04_traceSegment_037_1296_0054, g32p_row04_traceSegment_037_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1404 13 14, g32p_row04_traceSegment_037_1404_0013, g32p_row04_traceSegment_037_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1431 13 14, g32p_row04_traceSegment_037_1431_0013, g32p_row04_traceSegment_037_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1404 27 27, g32p_row04_traceSegment_037_1404_0027, g32p_row04_traceSegment_037_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1458 13 14, g32p_row04_traceSegment_037_1458_0013, g32p_row04_traceSegment_037_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1485 13 14, g32p_row04_traceSegment_037_1485_0013, g32p_row04_traceSegment_037_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1458 27 27, g32p_row04_traceSegment_037_1458_0027, g32p_row04_traceSegment_037_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1404 54 54, g32p_row04_traceSegment_037_1404_0054, g32p_row04_traceSegment_037_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1296 108 108, g32p_row04_traceSegment_037_1296_0108, g32p_row04_traceSegment_037_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1512 13 14, g32p_row04_traceSegment_037_1512_0013, g32p_row04_traceSegment_037_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1539 13 14, g32p_row04_traceSegment_037_1539_0013, g32p_row04_traceSegment_037_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1512 27 27, g32p_row04_traceSegment_037_1512_0027, g32p_row04_traceSegment_037_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1566 13 14, g32p_row04_traceSegment_037_1566_0013, g32p_row04_traceSegment_037_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1593 13 14, g32p_row04_traceSegment_037_1593_0013, g32p_row04_traceSegment_037_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1566 27 27, g32p_row04_traceSegment_037_1566_0027, g32p_row04_traceSegment_037_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1512 54 54, g32p_row04_traceSegment_037_1512_0054, g32p_row04_traceSegment_037_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1620 13 14, g32p_row04_traceSegment_037_1620_0013, g32p_row04_traceSegment_037_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1647 13 14, g32p_row04_traceSegment_037_1647_0013, g32p_row04_traceSegment_037_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1620 27 27, g32p_row04_traceSegment_037_1620_0027, g32p_row04_traceSegment_037_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1674 13 14, g32p_row04_traceSegment_037_1674_0013, g32p_row04_traceSegment_037_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_037 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_037 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_037_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_037 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1701 13 14, g32p_row04_traceSegment_037_1701_0013, g32p_row04_traceSegment_037_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_037 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1674 27 27, g32p_row04_traceSegment_037_1674_0027, g32p_row04_traceSegment_037_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_037 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1620 54 54, g32p_row04_traceSegment_037_1620_0054, g32p_row04_traceSegment_037_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_037 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1512 108 108, g32p_row04_traceSegment_037_1512_0108, g32p_row04_traceSegment_037_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_037_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_037 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 1296 216 216, g32p_row04_traceSegment_037_1296_0216, g32p_row04_traceSegment_037_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_037 864 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 864 432 432, g32p_row04_traceSegment_037_0864_0432, g32p_row04_traceSegment_037_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_037_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_037 0 1728 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_037 0 864 864, g32p_row04_traceSegment_037_0000_0864, g32p_row04_traceSegment_037_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 37 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_037_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_040 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 40 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_040_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 13 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 0 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 13 14, g32p_row04_traceSegment_040_0000_0013, g32p_row04_traceSegment_040_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 27 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 27 13 14, g32p_row04_traceSegment_040_0027_0013, g32p_row04_traceSegment_040_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 0 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 27 27, g32p_row04_traceSegment_040_0000_0027, g32p_row04_traceSegment_040_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 54 13 14, g32p_row04_traceSegment_040_0054_0013, g32p_row04_traceSegment_040_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 81 13 14, g32p_row04_traceSegment_040_0081_0013, g32p_row04_traceSegment_040_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 54 27 27, g32p_row04_traceSegment_040_0054_0027, g32p_row04_traceSegment_040_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 0 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 54 54, g32p_row04_traceSegment_040_0000_0054, g32p_row04_traceSegment_040_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 108 13 14, g32p_row04_traceSegment_040_0108_0013, g32p_row04_traceSegment_040_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 135 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 135 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 135 13 14, g32p_row04_traceSegment_040_0135_0013, g32p_row04_traceSegment_040_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 108 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 108 27 27, g32p_row04_traceSegment_040_0108_0027, g32p_row04_traceSegment_040_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 175 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 162 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 162 13 14, g32p_row04_traceSegment_040_0162_0013, g32p_row04_traceSegment_040_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 202 14 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 189 27 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 189 13 14, g32p_row04_traceSegment_040_0189_0013, g32p_row04_traceSegment_040_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 162 54 = [0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 162 27 27, g32p_row04_traceSegment_040_0162_0027, g32p_row04_traceSegment_040_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 108 108 = [0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 108 54 54, g32p_row04_traceSegment_040_0108_0054, g32p_row04_traceSegment_040_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 0 216 = [0, 4, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 108 108, g32p_row04_traceSegment_040_0000_0108, g32p_row04_traceSegment_040_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 216 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 229 14 = [0, 3, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 216 27 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 216 13 14, g32p_row04_traceSegment_040_0216_0013, g32p_row04_traceSegment_040_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 243 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 243 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 243 13 14, g32p_row04_traceSegment_040_0243_0013, g32p_row04_traceSegment_040_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 216 54 = [0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 216 27 27, g32p_row04_traceSegment_040_0216_0027, g32p_row04_traceSegment_040_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 270 13 14, g32p_row04_traceSegment_040_0270_0013, g32p_row04_traceSegment_040_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 297 13 14, g32p_row04_traceSegment_040_0297_0013, g32p_row04_traceSegment_040_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 270 27 27, g32p_row04_traceSegment_040_0270_0027, g32p_row04_traceSegment_040_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 216 108 = [0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 216 54 54, g32p_row04_traceSegment_040_0216_0054, g32p_row04_traceSegment_040_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 324 13 14, g32p_row04_traceSegment_040_0324_0013, g32p_row04_traceSegment_040_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 351 13 14, g32p_row04_traceSegment_040_0351_0013, g32p_row04_traceSegment_040_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 324 27 27, g32p_row04_traceSegment_040_0324_0027, g32p_row04_traceSegment_040_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 378 13 14, g32p_row04_traceSegment_040_0378_0013, g32p_row04_traceSegment_040_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 405 13 14, g32p_row04_traceSegment_040_0405_0013, g32p_row04_traceSegment_040_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 378 27 27, g32p_row04_traceSegment_040_0378_0027, g32p_row04_traceSegment_040_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 324 54 54, g32p_row04_traceSegment_040_0324_0054, g32p_row04_traceSegment_040_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 216 216 = [0, 5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 216 108 108, g32p_row04_traceSegment_040_0216_0108, g32p_row04_traceSegment_040_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_040 0 432 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 216 216, g32p_row04_traceSegment_040_0000_0216, g32p_row04_traceSegment_040_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 432 13 14, g32p_row04_traceSegment_040_0432_0013, g32p_row04_traceSegment_040_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 459 13 14, g32p_row04_traceSegment_040_0459_0013, g32p_row04_traceSegment_040_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 432 27 27, g32p_row04_traceSegment_040_0432_0027, g32p_row04_traceSegment_040_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 486 13 14, g32p_row04_traceSegment_040_0486_0013, g32p_row04_traceSegment_040_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 513 13 14, g32p_row04_traceSegment_040_0513_0013, g32p_row04_traceSegment_040_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 486 27 27, g32p_row04_traceSegment_040_0486_0027, g32p_row04_traceSegment_040_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 432 54 54, g32p_row04_traceSegment_040_0432_0054, g32p_row04_traceSegment_040_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 540 13 14, g32p_row04_traceSegment_040_0540_0013, g32p_row04_traceSegment_040_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 567 13 14, g32p_row04_traceSegment_040_0567_0013, g32p_row04_traceSegment_040_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 540 27 27, g32p_row04_traceSegment_040_0540_0027, g32p_row04_traceSegment_040_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 594 13 14, g32p_row04_traceSegment_040_0594_0013, g32p_row04_traceSegment_040_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 621 13 14, g32p_row04_traceSegment_040_0621_0013, g32p_row04_traceSegment_040_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 594 27 27, g32p_row04_traceSegment_040_0594_0027, g32p_row04_traceSegment_040_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 540 54 54, g32p_row04_traceSegment_040_0540_0054, g32p_row04_traceSegment_040_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 432 108 108, g32p_row04_traceSegment_040_0432_0108, g32p_row04_traceSegment_040_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 648 13 14, g32p_row04_traceSegment_040_0648_0013, g32p_row04_traceSegment_040_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 675 13 14, g32p_row04_traceSegment_040_0675_0013, g32p_row04_traceSegment_040_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 648 27 27, g32p_row04_traceSegment_040_0648_0027, g32p_row04_traceSegment_040_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 702 13 14, g32p_row04_traceSegment_040_0702_0013, g32p_row04_traceSegment_040_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 729 13 14, g32p_row04_traceSegment_040_0729_0013, g32p_row04_traceSegment_040_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 702 27 27, g32p_row04_traceSegment_040_0702_0027, g32p_row04_traceSegment_040_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 648 54 54, g32p_row04_traceSegment_040_0648_0054, g32p_row04_traceSegment_040_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 756 13 14, g32p_row04_traceSegment_040_0756_0013, g32p_row04_traceSegment_040_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 783 13 14, g32p_row04_traceSegment_040_0783_0013, g32p_row04_traceSegment_040_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 756 27 27, g32p_row04_traceSegment_040_0756_0027, g32p_row04_traceSegment_040_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 810 13 14, g32p_row04_traceSegment_040_0810_0013, g32p_row04_traceSegment_040_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 837 13 14, g32p_row04_traceSegment_040_0837_0013, g32p_row04_traceSegment_040_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 810 27 27, g32p_row04_traceSegment_040_0810_0027, g32p_row04_traceSegment_040_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 756 54 54, g32p_row04_traceSegment_040_0756_0054, g32p_row04_traceSegment_040_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 648 108 108, g32p_row04_traceSegment_040_0648_0108, g32p_row04_traceSegment_040_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_040 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 432 216 216, g32p_row04_traceSegment_040_0432_0216, g32p_row04_traceSegment_040_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_040 0 864 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 432 432, g32p_row04_traceSegment_040_0000_0432, g32p_row04_traceSegment_040_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 877 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 864 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 864 13 14, g32p_row04_traceSegment_040_0864_0013, g32p_row04_traceSegment_040_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 891 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 891 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 891 13 14, g32p_row04_traceSegment_040_0891_0013, g32p_row04_traceSegment_040_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 864 54 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 864 27 27, g32p_row04_traceSegment_040_0864_0027, g32p_row04_traceSegment_040_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 918 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 931 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 918 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 918 13 14, g32p_row04_traceSegment_040_0918_0013, g32p_row04_traceSegment_040_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 945 13 14, g32p_row04_traceSegment_040_0945_0013, g32p_row04_traceSegment_040_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 918 54 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 918 27 27, g32p_row04_traceSegment_040_0918_0027, g32p_row04_traceSegment_040_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 864 108 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 864 54 54, g32p_row04_traceSegment_040_0864_0054, g32p_row04_traceSegment_040_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 972 13 14, g32p_row04_traceSegment_040_0972_0013, g32p_row04_traceSegment_040_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1012 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 999 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 999 13 14, g32p_row04_traceSegment_040_0999_0013, g32p_row04_traceSegment_040_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 972 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 972 27 27, g32p_row04_traceSegment_040_0972_0027, g32p_row04_traceSegment_040_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1026 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1026 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1026 13 14, g32p_row04_traceSegment_040_1026_0013, g32p_row04_traceSegment_040_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1053 13 14, g32p_row04_traceSegment_040_1053_0013, g32p_row04_traceSegment_040_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1026 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1026 27 27, g32p_row04_traceSegment_040_1026_0027, g32p_row04_traceSegment_040_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 972 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 972 54 54, g32p_row04_traceSegment_040_0972_0054, g32p_row04_traceSegment_040_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 864 216 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 864 108 108, g32p_row04_traceSegment_040_0864_0108, g32p_row04_traceSegment_040_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1080 13 14, g32p_row04_traceSegment_040_1080_0013, g32p_row04_traceSegment_040_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1107 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1107 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1107 13 14, g32p_row04_traceSegment_040_1107_0013, g32p_row04_traceSegment_040_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1080 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1080 27 27, g32p_row04_traceSegment_040_1080_0027, g32p_row04_traceSegment_040_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1134 13 14, g32p_row04_traceSegment_040_1134_0013, g32p_row04_traceSegment_040_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1161 13 14, g32p_row04_traceSegment_040_1161_0013, g32p_row04_traceSegment_040_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1134 27 27, g32p_row04_traceSegment_040_1134_0027, g32p_row04_traceSegment_040_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 1080 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1080 54 54, g32p_row04_traceSegment_040_1080_0054, g32p_row04_traceSegment_040_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1188 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1188 13 14, g32p_row04_traceSegment_040_1188_0013, g32p_row04_traceSegment_040_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1215 13 14, g32p_row04_traceSegment_040_1215_0013, g32p_row04_traceSegment_040_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1188 27 27, g32p_row04_traceSegment_040_1188_0027, g32p_row04_traceSegment_040_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1242 13 14, g32p_row04_traceSegment_040_1242_0013, g32p_row04_traceSegment_040_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1269 13 14, g32p_row04_traceSegment_040_1269_0013, g32p_row04_traceSegment_040_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1242 27 27, g32p_row04_traceSegment_040_1242_0027, g32p_row04_traceSegment_040_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 1188 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1188 54 54, g32p_row04_traceSegment_040_1188_0054, g32p_row04_traceSegment_040_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 1080 216 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1080 108 108, g32p_row04_traceSegment_040_1080_0108, g32p_row04_traceSegment_040_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_040 864 432 = [0, 5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 864 216 216, g32p_row04_traceSegment_040_0864_0216, g32p_row04_traceSegment_040_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1296 13 14, g32p_row04_traceSegment_040_1296_0013, g32p_row04_traceSegment_040_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1323 13 14, g32p_row04_traceSegment_040_1323_0013, g32p_row04_traceSegment_040_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1296 27 27, g32p_row04_traceSegment_040_1296_0027, g32p_row04_traceSegment_040_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1350 13 14, g32p_row04_traceSegment_040_1350_0013, g32p_row04_traceSegment_040_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1377 13 14, g32p_row04_traceSegment_040_1377_0013, g32p_row04_traceSegment_040_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1350 27 27, g32p_row04_traceSegment_040_1350_0027, g32p_row04_traceSegment_040_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1296 54 54, g32p_row04_traceSegment_040_1296_0054, g32p_row04_traceSegment_040_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1404 13 14, g32p_row04_traceSegment_040_1404_0013, g32p_row04_traceSegment_040_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1431 13 14, g32p_row04_traceSegment_040_1431_0013, g32p_row04_traceSegment_040_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1404 27 27, g32p_row04_traceSegment_040_1404_0027, g32p_row04_traceSegment_040_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1458 13 14, g32p_row04_traceSegment_040_1458_0013, g32p_row04_traceSegment_040_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1485 13 14, g32p_row04_traceSegment_040_1485_0013, g32p_row04_traceSegment_040_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1458 27 27, g32p_row04_traceSegment_040_1458_0027, g32p_row04_traceSegment_040_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1404 54 54, g32p_row04_traceSegment_040_1404_0054, g32p_row04_traceSegment_040_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1296 108 108, g32p_row04_traceSegment_040_1296_0108, g32p_row04_traceSegment_040_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1512 13 14, g32p_row04_traceSegment_040_1512_0013, g32p_row04_traceSegment_040_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1539 13 14, g32p_row04_traceSegment_040_1539_0013, g32p_row04_traceSegment_040_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1512 27 27, g32p_row04_traceSegment_040_1512_0027, g32p_row04_traceSegment_040_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1566 13 14, g32p_row04_traceSegment_040_1566_0013, g32p_row04_traceSegment_040_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1593 13 14, g32p_row04_traceSegment_040_1593_0013, g32p_row04_traceSegment_040_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1566 27 27, g32p_row04_traceSegment_040_1566_0027, g32p_row04_traceSegment_040_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1512 54 54, g32p_row04_traceSegment_040_1512_0054, g32p_row04_traceSegment_040_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1620 13 14, g32p_row04_traceSegment_040_1620_0013, g32p_row04_traceSegment_040_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1647 13 14, g32p_row04_traceSegment_040_1647_0013, g32p_row04_traceSegment_040_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1620 27 27, g32p_row04_traceSegment_040_1620_0027, g32p_row04_traceSegment_040_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1674 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1687 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1674 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1674 13 14, g32p_row04_traceSegment_040_1674_0013, g32p_row04_traceSegment_040_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_040 1701 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_040 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_040_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_040 1701 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1701 13 14, g32p_row04_traceSegment_040_1701_0013, g32p_row04_traceSegment_040_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_040 1674 54 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1674 27 27, g32p_row04_traceSegment_040_1674_0027, g32p_row04_traceSegment_040_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_040 1620 108 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1620 54 54, g32p_row04_traceSegment_040_1620_0054, g32p_row04_traceSegment_040_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_040 1512 216 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1512 108 108, g32p_row04_traceSegment_040_1512_0108, g32p_row04_traceSegment_040_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_040_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_040 1296 432 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 1296 216 216, g32p_row04_traceSegment_040_1296_0216, g32p_row04_traceSegment_040_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_040 864 864 = [0, 7, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 864 432 432, g32p_row04_traceSegment_040_0864_0432, g32p_row04_traceSegment_040_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_040_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_040 0 1728 = [0, 16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_040 0 864 864, g32p_row04_traceSegment_040_0000_0864, g32p_row04_traceSegment_040_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 40 = [0, 16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_040_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_041 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 41 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_041_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 13 14, g32p_row04_traceSegment_041_0000_0013, g32p_row04_traceSegment_041_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 27 13 14, g32p_row04_traceSegment_041_0027_0013, g32p_row04_traceSegment_041_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 27 27, g32p_row04_traceSegment_041_0000_0027, g32p_row04_traceSegment_041_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 54 13 14, g32p_row04_traceSegment_041_0054_0013, g32p_row04_traceSegment_041_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 81 13 14, g32p_row04_traceSegment_041_0081_0013, g32p_row04_traceSegment_041_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 54 27 27, g32p_row04_traceSegment_041_0054_0027, g32p_row04_traceSegment_041_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 54 54, g32p_row04_traceSegment_041_0000_0054, g32p_row04_traceSegment_041_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 108 13 14, g32p_row04_traceSegment_041_0108_0013, g32p_row04_traceSegment_041_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 135 13 14, g32p_row04_traceSegment_041_0135_0013, g32p_row04_traceSegment_041_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 108 27 27, g32p_row04_traceSegment_041_0108_0027, g32p_row04_traceSegment_041_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 162 13 14, g32p_row04_traceSegment_041_0162_0013, g32p_row04_traceSegment_041_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 189 13 14, g32p_row04_traceSegment_041_0189_0013, g32p_row04_traceSegment_041_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 162 27 27, g32p_row04_traceSegment_041_0162_0027, g32p_row04_traceSegment_041_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 108 54 54, g32p_row04_traceSegment_041_0108_0054, g32p_row04_traceSegment_041_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 108 108, g32p_row04_traceSegment_041_0000_0108, g32p_row04_traceSegment_041_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 216 13 14, g32p_row04_traceSegment_041_0216_0013, g32p_row04_traceSegment_041_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 243 13 14, g32p_row04_traceSegment_041_0243_0013, g32p_row04_traceSegment_041_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 216 27 27, g32p_row04_traceSegment_041_0216_0027, g32p_row04_traceSegment_041_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 283 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 270 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 270 13 14, g32p_row04_traceSegment_041_0270_0013, g32p_row04_traceSegment_041_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 297 13 = [2, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 310 14 = [1, 0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 297 27 = [3, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 297 13 14, g32p_row04_traceSegment_041_0297_0013, g32p_row04_traceSegment_041_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 270 54 = [4, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 270 27 27, g32p_row04_traceSegment_041_0270_0027, g32p_row04_traceSegment_041_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 216 108 = [4, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 216 54 54, g32p_row04_traceSegment_041_0216_0054, g32p_row04_traceSegment_041_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 324 13 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 337 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 324 27 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 324 13 14, g32p_row04_traceSegment_041_0324_0013, g32p_row04_traceSegment_041_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 351 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 364 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 351 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 351 13 14, g32p_row04_traceSegment_041_0351_0013, g32p_row04_traceSegment_041_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 324 54 = [2, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 324 27 27, g32p_row04_traceSegment_041_0324_0027, g32p_row04_traceSegment_041_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 378 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 391 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 378 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 378 13 14, g32p_row04_traceSegment_041_0378_0013, g32p_row04_traceSegment_041_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 405 13 14, g32p_row04_traceSegment_041_0405_0013, g32p_row04_traceSegment_041_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 378 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 378 27 27, g32p_row04_traceSegment_041_0378_0027, g32p_row04_traceSegment_041_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 324 108 = [2, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 324 54 54, g32p_row04_traceSegment_041_0324_0054, g32p_row04_traceSegment_041_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 216 216 = [6, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 216 108 108, g32p_row04_traceSegment_041_0216_0108, g32p_row04_traceSegment_041_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_041 0 432 = [6, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 216 216, g32p_row04_traceSegment_041_0000_0216, g32p_row04_traceSegment_041_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 432 13 14, g32p_row04_traceSegment_041_0432_0013, g32p_row04_traceSegment_041_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 459 13 14, g32p_row04_traceSegment_041_0459_0013, g32p_row04_traceSegment_041_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 432 27 27, g32p_row04_traceSegment_041_0432_0027, g32p_row04_traceSegment_041_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 486 13 14, g32p_row04_traceSegment_041_0486_0013, g32p_row04_traceSegment_041_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 513 13 14, g32p_row04_traceSegment_041_0513_0013, g32p_row04_traceSegment_041_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 486 27 27, g32p_row04_traceSegment_041_0486_0027, g32p_row04_traceSegment_041_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 432 54 54, g32p_row04_traceSegment_041_0432_0054, g32p_row04_traceSegment_041_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 540 13 14, g32p_row04_traceSegment_041_0540_0013, g32p_row04_traceSegment_041_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 567 13 14, g32p_row04_traceSegment_041_0567_0013, g32p_row04_traceSegment_041_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 540 27 27, g32p_row04_traceSegment_041_0540_0027, g32p_row04_traceSegment_041_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 594 13 14, g32p_row04_traceSegment_041_0594_0013, g32p_row04_traceSegment_041_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 621 13 14, g32p_row04_traceSegment_041_0621_0013, g32p_row04_traceSegment_041_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 594 27 27, g32p_row04_traceSegment_041_0594_0027, g32p_row04_traceSegment_041_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 540 54 54, g32p_row04_traceSegment_041_0540_0054, g32p_row04_traceSegment_041_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 432 108 108, g32p_row04_traceSegment_041_0432_0108, g32p_row04_traceSegment_041_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 648 13 14, g32p_row04_traceSegment_041_0648_0013, g32p_row04_traceSegment_041_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 675 13 14, g32p_row04_traceSegment_041_0675_0013, g32p_row04_traceSegment_041_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 648 27 27, g32p_row04_traceSegment_041_0648_0027, g32p_row04_traceSegment_041_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 702 13 14, g32p_row04_traceSegment_041_0702_0013, g32p_row04_traceSegment_041_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 729 13 14, g32p_row04_traceSegment_041_0729_0013, g32p_row04_traceSegment_041_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 702 27 27, g32p_row04_traceSegment_041_0702_0027, g32p_row04_traceSegment_041_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 648 54 54, g32p_row04_traceSegment_041_0648_0054, g32p_row04_traceSegment_041_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 756 13 14, g32p_row04_traceSegment_041_0756_0013, g32p_row04_traceSegment_041_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 783 13 14, g32p_row04_traceSegment_041_0783_0013, g32p_row04_traceSegment_041_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 756 27 27, g32p_row04_traceSegment_041_0756_0027, g32p_row04_traceSegment_041_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 810 13 14, g32p_row04_traceSegment_041_0810_0013, g32p_row04_traceSegment_041_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 837 13 14, g32p_row04_traceSegment_041_0837_0013, g32p_row04_traceSegment_041_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 810 27 27, g32p_row04_traceSegment_041_0810_0027, g32p_row04_traceSegment_041_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 756 54 54, g32p_row04_traceSegment_041_0756_0054, g32p_row04_traceSegment_041_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 648 108 108, g32p_row04_traceSegment_041_0648_0108, g32p_row04_traceSegment_041_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_041 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 432 216 216, g32p_row04_traceSegment_041_0432_0216, g32p_row04_traceSegment_041_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_041 0 864 = [6, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 432 432, g32p_row04_traceSegment_041_0000_0432, g32p_row04_traceSegment_041_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 864 13 14, g32p_row04_traceSegment_041_0864_0013, g32p_row04_traceSegment_041_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 891 13 14, g32p_row04_traceSegment_041_0891_0013, g32p_row04_traceSegment_041_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 864 27 27, g32p_row04_traceSegment_041_0864_0027, g32p_row04_traceSegment_041_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 918 13 14, g32p_row04_traceSegment_041_0918_0013, g32p_row04_traceSegment_041_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 945 13 14, g32p_row04_traceSegment_041_0945_0013, g32p_row04_traceSegment_041_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 918 27 27, g32p_row04_traceSegment_041_0918_0027, g32p_row04_traceSegment_041_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 864 54 54, g32p_row04_traceSegment_041_0864_0054, g32p_row04_traceSegment_041_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 972 13 14, g32p_row04_traceSegment_041_0972_0013, g32p_row04_traceSegment_041_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 999 13 14, g32p_row04_traceSegment_041_0999_0013, g32p_row04_traceSegment_041_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 972 27 27, g32p_row04_traceSegment_041_0972_0027, g32p_row04_traceSegment_041_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1026 13 14, g32p_row04_traceSegment_041_1026_0013, g32p_row04_traceSegment_041_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1053 13 14, g32p_row04_traceSegment_041_1053_0013, g32p_row04_traceSegment_041_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1026 27 27, g32p_row04_traceSegment_041_1026_0027, g32p_row04_traceSegment_041_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 972 54 54, g32p_row04_traceSegment_041_0972_0054, g32p_row04_traceSegment_041_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 864 108 108, g32p_row04_traceSegment_041_0864_0108, g32p_row04_traceSegment_041_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1080 13 14, g32p_row04_traceSegment_041_1080_0013, g32p_row04_traceSegment_041_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1107 13 14, g32p_row04_traceSegment_041_1107_0013, g32p_row04_traceSegment_041_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1080 27 27, g32p_row04_traceSegment_041_1080_0027, g32p_row04_traceSegment_041_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1134 13 14, g32p_row04_traceSegment_041_1134_0013, g32p_row04_traceSegment_041_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1161 13 14, g32p_row04_traceSegment_041_1161_0013, g32p_row04_traceSegment_041_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1134 27 27, g32p_row04_traceSegment_041_1134_0027, g32p_row04_traceSegment_041_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1080 54 54, g32p_row04_traceSegment_041_1080_0054, g32p_row04_traceSegment_041_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1201 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1188 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1188 13 14, g32p_row04_traceSegment_041_1188_0013, g32p_row04_traceSegment_041_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1215 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1228 14 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1215 27 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1215 13 14, g32p_row04_traceSegment_041_1215_0013, g32p_row04_traceSegment_041_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1188 54 = [6, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1188 27 27, g32p_row04_traceSegment_041_1188_0027, g32p_row04_traceSegment_041_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1242 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1255 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1242 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1242 13 14, g32p_row04_traceSegment_041_1242_0013, g32p_row04_traceSegment_041_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1269 13 14, g32p_row04_traceSegment_041_1269_0013, g32p_row04_traceSegment_041_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1242 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1242 27 27, g32p_row04_traceSegment_041_1242_0027, g32p_row04_traceSegment_041_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 1188 108 = [6, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1188 54 54, g32p_row04_traceSegment_041_1188_0054, g32p_row04_traceSegment_041_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 1080 216 = [6, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1080 108 108, g32p_row04_traceSegment_041_1080_0108, g32p_row04_traceSegment_041_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_041 864 432 = [6, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 864 216 216, g32p_row04_traceSegment_041_0864_0216, g32p_row04_traceSegment_041_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1296 13 14, g32p_row04_traceSegment_041_1296_0013, g32p_row04_traceSegment_041_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1323 13 14, g32p_row04_traceSegment_041_1323_0013, g32p_row04_traceSegment_041_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1296 27 27, g32p_row04_traceSegment_041_1296_0027, g32p_row04_traceSegment_041_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1363 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1350 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1350 13 14, g32p_row04_traceSegment_041_1350_0013, g32p_row04_traceSegment_041_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1377 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1390 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1377 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1377 13 14, g32p_row04_traceSegment_041_1377_0013, g32p_row04_traceSegment_041_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1350 54 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1350 27 27, g32p_row04_traceSegment_041_1350_0027, g32p_row04_traceSegment_041_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 1296 108 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1296 54 54, g32p_row04_traceSegment_041_1296_0054, g32p_row04_traceSegment_041_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1417 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1404 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1404 13 14, g32p_row04_traceSegment_041_1404_0013, g32p_row04_traceSegment_041_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1444 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1431 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1431 13 14, g32p_row04_traceSegment_041_1431_0013, g32p_row04_traceSegment_041_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1404 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1404 27 27, g32p_row04_traceSegment_041_1404_0027, g32p_row04_traceSegment_041_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1458 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1471 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1458 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1458 13 14, g32p_row04_traceSegment_041_1458_0013, g32p_row04_traceSegment_041_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1485 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1485 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1485 13 14, g32p_row04_traceSegment_041_1485_0013, g32p_row04_traceSegment_041_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1458 54 = [3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1458 27 27, g32p_row04_traceSegment_041_1458_0027, g32p_row04_traceSegment_041_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 1404 108 = [5, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1404 54 54, g32p_row04_traceSegment_041_1404_0054, g32p_row04_traceSegment_041_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 1296 216 = [12, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1296 108 108, g32p_row04_traceSegment_041_1296_0108, g32p_row04_traceSegment_041_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1512 13 14, g32p_row04_traceSegment_041_1512_0013, g32p_row04_traceSegment_041_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1539 13 14, g32p_row04_traceSegment_041_1539_0013, g32p_row04_traceSegment_041_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1512 27 27, g32p_row04_traceSegment_041_1512_0027, g32p_row04_traceSegment_041_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1566 13 14, g32p_row04_traceSegment_041_1566_0013, g32p_row04_traceSegment_041_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1593 13 14, g32p_row04_traceSegment_041_1593_0013, g32p_row04_traceSegment_041_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1566 27 27, g32p_row04_traceSegment_041_1566_0027, g32p_row04_traceSegment_041_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1512 54 54, g32p_row04_traceSegment_041_1512_0054, g32p_row04_traceSegment_041_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1620 13 14, g32p_row04_traceSegment_041_1620_0013, g32p_row04_traceSegment_041_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1647 13 14, g32p_row04_traceSegment_041_1647_0013, g32p_row04_traceSegment_041_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1620 27 27, g32p_row04_traceSegment_041_1620_0027, g32p_row04_traceSegment_041_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1674 13 14, g32p_row04_traceSegment_041_1674_0013, g32p_row04_traceSegment_041_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_041 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_041 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_041_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_041 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1701 13 14, g32p_row04_traceSegment_041_1701_0013, g32p_row04_traceSegment_041_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_041 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1674 27 27, g32p_row04_traceSegment_041_1674_0027, g32p_row04_traceSegment_041_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_041 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1620 54 54, g32p_row04_traceSegment_041_1620_0054, g32p_row04_traceSegment_041_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_041 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1512 108 108, g32p_row04_traceSegment_041_1512_0108, g32p_row04_traceSegment_041_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_041_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_041 1296 432 = [12, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 1296 216 216, g32p_row04_traceSegment_041_1296_0216, g32p_row04_traceSegment_041_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_041 864 864 = [18, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 864 432 432, g32p_row04_traceSegment_041_0864_0432, g32p_row04_traceSegment_041_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_041_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_041 0 1728 = [24, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_041 0 864 864, g32p_row04_traceSegment_041_0000_0864, g32p_row04_traceSegment_041_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 41 = [24, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_041_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_043 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 43 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_043_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 13 14, g32p_row04_traceSegment_043_0000_0013, g32p_row04_traceSegment_043_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 27 13 14, g32p_row04_traceSegment_043_0027_0013, g32p_row04_traceSegment_043_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 27 27, g32p_row04_traceSegment_043_0000_0027, g32p_row04_traceSegment_043_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 54 13 14, g32p_row04_traceSegment_043_0054_0013, g32p_row04_traceSegment_043_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 81 13 14, g32p_row04_traceSegment_043_0081_0013, g32p_row04_traceSegment_043_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 54 27 27, g32p_row04_traceSegment_043_0054_0027, g32p_row04_traceSegment_043_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 54 54, g32p_row04_traceSegment_043_0000_0054, g32p_row04_traceSegment_043_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 108 13 14, g32p_row04_traceSegment_043_0108_0013, g32p_row04_traceSegment_043_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 135 13 14, g32p_row04_traceSegment_043_0135_0013, g32p_row04_traceSegment_043_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 108 27 27, g32p_row04_traceSegment_043_0108_0027, g32p_row04_traceSegment_043_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 162 13 14, g32p_row04_traceSegment_043_0162_0013, g32p_row04_traceSegment_043_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 189 13 14, g32p_row04_traceSegment_043_0189_0013, g32p_row04_traceSegment_043_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 162 27 27, g32p_row04_traceSegment_043_0162_0027, g32p_row04_traceSegment_043_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 108 54 54, g32p_row04_traceSegment_043_0108_0054, g32p_row04_traceSegment_043_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 108 108, g32p_row04_traceSegment_043_0000_0108, g32p_row04_traceSegment_043_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 216 13 14, g32p_row04_traceSegment_043_0216_0013, g32p_row04_traceSegment_043_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 243 13 14, g32p_row04_traceSegment_043_0243_0013, g32p_row04_traceSegment_043_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 216 27 27, g32p_row04_traceSegment_043_0216_0027, g32p_row04_traceSegment_043_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 270 13 14, g32p_row04_traceSegment_043_0270_0013, g32p_row04_traceSegment_043_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 297 13 14, g32p_row04_traceSegment_043_0297_0013, g32p_row04_traceSegment_043_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 270 27 27, g32p_row04_traceSegment_043_0270_0027, g32p_row04_traceSegment_043_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 216 54 54, g32p_row04_traceSegment_043_0216_0054, g32p_row04_traceSegment_043_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 324 13 14, g32p_row04_traceSegment_043_0324_0013, g32p_row04_traceSegment_043_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 351 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 351 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 351 13 14, g32p_row04_traceSegment_043_0351_0013, g32p_row04_traceSegment_043_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 324 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 324 27 27, g32p_row04_traceSegment_043_0324_0027, g32p_row04_traceSegment_043_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 378 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 391 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 378 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 378 13 14, g32p_row04_traceSegment_043_0378_0013, g32p_row04_traceSegment_043_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 418 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 405 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 405 13 14, g32p_row04_traceSegment_043_0405_0013, g32p_row04_traceSegment_043_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 378 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 378 27 27, g32p_row04_traceSegment_043_0378_0027, g32p_row04_traceSegment_043_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 324 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 324 54 54, g32p_row04_traceSegment_043_0324_0054, g32p_row04_traceSegment_043_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 216 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 216 108 108, g32p_row04_traceSegment_043_0216_0108, g32p_row04_traceSegment_043_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_043 0 432 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 216 216, g32p_row04_traceSegment_043_0000_0216, g32p_row04_traceSegment_043_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 432 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 445 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 432 27 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 432 13 14, g32p_row04_traceSegment_043_0432_0013, g32p_row04_traceSegment_043_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 459 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 472 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 459 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 459 13 14, g32p_row04_traceSegment_043_0459_0013, g32p_row04_traceSegment_043_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 432 54 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 432 27 27, g32p_row04_traceSegment_043_0432_0027, g32p_row04_traceSegment_043_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 486 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 486 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 486 13 14, g32p_row04_traceSegment_043_0486_0013, g32p_row04_traceSegment_043_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 513 13 14, g32p_row04_traceSegment_043_0513_0013, g32p_row04_traceSegment_043_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 486 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 486 27 27, g32p_row04_traceSegment_043_0486_0027, g32p_row04_traceSegment_043_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 432 108 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 432 54 54, g32p_row04_traceSegment_043_0432_0054, g32p_row04_traceSegment_043_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 540 13 14, g32p_row04_traceSegment_043_0540_0013, g32p_row04_traceSegment_043_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 567 13 14, g32p_row04_traceSegment_043_0567_0013, g32p_row04_traceSegment_043_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 540 27 27, g32p_row04_traceSegment_043_0540_0027, g32p_row04_traceSegment_043_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 594 13 14, g32p_row04_traceSegment_043_0594_0013, g32p_row04_traceSegment_043_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 621 13 14, g32p_row04_traceSegment_043_0621_0013, g32p_row04_traceSegment_043_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 594 27 27, g32p_row04_traceSegment_043_0594_0027, g32p_row04_traceSegment_043_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 540 54 54, g32p_row04_traceSegment_043_0540_0054, g32p_row04_traceSegment_043_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 432 216 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 432 108 108, g32p_row04_traceSegment_043_0432_0108, g32p_row04_traceSegment_043_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 648 13 14, g32p_row04_traceSegment_043_0648_0013, g32p_row04_traceSegment_043_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 675 13 14, g32p_row04_traceSegment_043_0675_0013, g32p_row04_traceSegment_043_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 648 27 27, g32p_row04_traceSegment_043_0648_0027, g32p_row04_traceSegment_043_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 702 13 14, g32p_row04_traceSegment_043_0702_0013, g32p_row04_traceSegment_043_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 729 13 14, g32p_row04_traceSegment_043_0729_0013, g32p_row04_traceSegment_043_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 702 27 27, g32p_row04_traceSegment_043_0702_0027, g32p_row04_traceSegment_043_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 648 54 54, g32p_row04_traceSegment_043_0648_0054, g32p_row04_traceSegment_043_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 756 13 14, g32p_row04_traceSegment_043_0756_0013, g32p_row04_traceSegment_043_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 783 13 14, g32p_row04_traceSegment_043_0783_0013, g32p_row04_traceSegment_043_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 756 27 27, g32p_row04_traceSegment_043_0756_0027, g32p_row04_traceSegment_043_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 810 13 14, g32p_row04_traceSegment_043_0810_0013, g32p_row04_traceSegment_043_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 837 13 14, g32p_row04_traceSegment_043_0837_0013, g32p_row04_traceSegment_043_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 810 27 27, g32p_row04_traceSegment_043_0810_0027, g32p_row04_traceSegment_043_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 756 54 54, g32p_row04_traceSegment_043_0756_0054, g32p_row04_traceSegment_043_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 648 108 108, g32p_row04_traceSegment_043_0648_0108, g32p_row04_traceSegment_043_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_043 432 432 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 432 216 216, g32p_row04_traceSegment_043_0432_0216, g32p_row04_traceSegment_043_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_043 0 864 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 432 432, g32p_row04_traceSegment_043_0000_0432, g32p_row04_traceSegment_043_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 864 13 14, g32p_row04_traceSegment_043_0864_0013, g32p_row04_traceSegment_043_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 891 13 14, g32p_row04_traceSegment_043_0891_0013, g32p_row04_traceSegment_043_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 864 27 27, g32p_row04_traceSegment_043_0864_0027, g32p_row04_traceSegment_043_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 918 13 14, g32p_row04_traceSegment_043_0918_0013, g32p_row04_traceSegment_043_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 945 13 14, g32p_row04_traceSegment_043_0945_0013, g32p_row04_traceSegment_043_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 918 27 27, g32p_row04_traceSegment_043_0918_0027, g32p_row04_traceSegment_043_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 864 54 54, g32p_row04_traceSegment_043_0864_0054, g32p_row04_traceSegment_043_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 972 13 14, g32p_row04_traceSegment_043_0972_0013, g32p_row04_traceSegment_043_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 999 13 14, g32p_row04_traceSegment_043_0999_0013, g32p_row04_traceSegment_043_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 972 27 27, g32p_row04_traceSegment_043_0972_0027, g32p_row04_traceSegment_043_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1026 13 14, g32p_row04_traceSegment_043_1026_0013, g32p_row04_traceSegment_043_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1053 13 14, g32p_row04_traceSegment_043_1053_0013, g32p_row04_traceSegment_043_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1026 27 27, g32p_row04_traceSegment_043_1026_0027, g32p_row04_traceSegment_043_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 972 54 54, g32p_row04_traceSegment_043_0972_0054, g32p_row04_traceSegment_043_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 864 108 108, g32p_row04_traceSegment_043_0864_0108, g32p_row04_traceSegment_043_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1080 13 14, g32p_row04_traceSegment_043_1080_0013, g32p_row04_traceSegment_043_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1107 13 14, g32p_row04_traceSegment_043_1107_0013, g32p_row04_traceSegment_043_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1080 27 27, g32p_row04_traceSegment_043_1080_0027, g32p_row04_traceSegment_043_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1134 13 14, g32p_row04_traceSegment_043_1134_0013, g32p_row04_traceSegment_043_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1161 13 14, g32p_row04_traceSegment_043_1161_0013, g32p_row04_traceSegment_043_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1134 27 27, g32p_row04_traceSegment_043_1134_0027, g32p_row04_traceSegment_043_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1080 54 54, g32p_row04_traceSegment_043_1080_0054, g32p_row04_traceSegment_043_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1188 13 14, g32p_row04_traceSegment_043_1188_0013, g32p_row04_traceSegment_043_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1215 13 14, g32p_row04_traceSegment_043_1215_0013, g32p_row04_traceSegment_043_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1188 27 27, g32p_row04_traceSegment_043_1188_0027, g32p_row04_traceSegment_043_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1242 13 14, g32p_row04_traceSegment_043_1242_0013, g32p_row04_traceSegment_043_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1282 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1269 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1269 13 14, g32p_row04_traceSegment_043_1269_0013, g32p_row04_traceSegment_043_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1242 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1242 27 27, g32p_row04_traceSegment_043_1242_0027, g32p_row04_traceSegment_043_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 1188 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1188 54 54, g32p_row04_traceSegment_043_1188_0054, g32p_row04_traceSegment_043_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 1080 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1080 108 108, g32p_row04_traceSegment_043_1080_0108, g32p_row04_traceSegment_043_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_043 864 432 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 864 216 216, g32p_row04_traceSegment_043_0864_0216, g32p_row04_traceSegment_043_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1296 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1309 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1296 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1296 13 14, g32p_row04_traceSegment_043_1296_0013, g32p_row04_traceSegment_043_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1336 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1323 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1323 13 14, g32p_row04_traceSegment_043_1323_0013, g32p_row04_traceSegment_043_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1296 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1296 27 27, g32p_row04_traceSegment_043_1296_0027, g32p_row04_traceSegment_043_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1350 13 14, g32p_row04_traceSegment_043_1350_0013, g32p_row04_traceSegment_043_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1377 13 14, g32p_row04_traceSegment_043_1377_0013, g32p_row04_traceSegment_043_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1350 27 27, g32p_row04_traceSegment_043_1350_0027, g32p_row04_traceSegment_043_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 1296 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1296 54 54, g32p_row04_traceSegment_043_1296_0054, g32p_row04_traceSegment_043_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1404 13 14, g32p_row04_traceSegment_043_1404_0013, g32p_row04_traceSegment_043_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1431 13 14, g32p_row04_traceSegment_043_1431_0013, g32p_row04_traceSegment_043_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1404 27 27, g32p_row04_traceSegment_043_1404_0027, g32p_row04_traceSegment_043_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1458 13 14, g32p_row04_traceSegment_043_1458_0013, g32p_row04_traceSegment_043_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1498 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1485 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1485 13 14, g32p_row04_traceSegment_043_1485_0013, g32p_row04_traceSegment_043_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1458 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1458 27 27, g32p_row04_traceSegment_043_1458_0027, g32p_row04_traceSegment_043_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 1404 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1404 54 54, g32p_row04_traceSegment_043_1404_0054, g32p_row04_traceSegment_043_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 1296 216 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1296 108 108, g32p_row04_traceSegment_043_1296_0108, g32p_row04_traceSegment_043_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1512 13 14, g32p_row04_traceSegment_043_1512_0013, g32p_row04_traceSegment_043_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1539 13 14, g32p_row04_traceSegment_043_1539_0013, g32p_row04_traceSegment_043_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1512 27 27, g32p_row04_traceSegment_043_1512_0027, g32p_row04_traceSegment_043_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1566 13 14, g32p_row04_traceSegment_043_1566_0013, g32p_row04_traceSegment_043_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1593 13 14, g32p_row04_traceSegment_043_1593_0013, g32p_row04_traceSegment_043_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1566 27 27, g32p_row04_traceSegment_043_1566_0027, g32p_row04_traceSegment_043_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1512 54 54, g32p_row04_traceSegment_043_1512_0054, g32p_row04_traceSegment_043_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1620 13 14, g32p_row04_traceSegment_043_1620_0013, g32p_row04_traceSegment_043_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1647 13 14, g32p_row04_traceSegment_043_1647_0013, g32p_row04_traceSegment_043_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1620 27 27, g32p_row04_traceSegment_043_1620_0027, g32p_row04_traceSegment_043_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1674 13 14, g32p_row04_traceSegment_043_1674_0013, g32p_row04_traceSegment_043_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_043 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_043 1714 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_043_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_043 1701 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1701 13 14, g32p_row04_traceSegment_043_1701_0013, g32p_row04_traceSegment_043_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_043 1674 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1674 27 27, g32p_row04_traceSegment_043_1674_0027, g32p_row04_traceSegment_043_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_043 1620 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1620 54 54, g32p_row04_traceSegment_043_1620_0054, g32p_row04_traceSegment_043_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_043 1512 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1512 108 108, g32p_row04_traceSegment_043_1512_0108, g32p_row04_traceSegment_043_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_043_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_043 1296 432 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 1296 216 216, g32p_row04_traceSegment_043_1296_0216, g32p_row04_traceSegment_043_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_043 864 864 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 864 432 432, g32p_row04_traceSegment_043_0864_0432, g32p_row04_traceSegment_043_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_043_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_043 0 1728 = [0, 32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_043 0 864 864, g32p_row04_traceSegment_043_0000_0864, g32p_row04_traceSegment_043_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 43 = [0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_043_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_044_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 13 14, g32p_row04_traceSegment_044_0000_0013, g32p_row04_traceSegment_044_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 27 13 14, g32p_row04_traceSegment_044_0027_0013, g32p_row04_traceSegment_044_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 27 27, g32p_row04_traceSegment_044_0000_0027, g32p_row04_traceSegment_044_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 54 13 14, g32p_row04_traceSegment_044_0054_0013, g32p_row04_traceSegment_044_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 81 13 14, g32p_row04_traceSegment_044_0081_0013, g32p_row04_traceSegment_044_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 54 27 27, g32p_row04_traceSegment_044_0054_0027, g32p_row04_traceSegment_044_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 54 54, g32p_row04_traceSegment_044_0000_0054, g32p_row04_traceSegment_044_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 108 13 14, g32p_row04_traceSegment_044_0108_0013, g32p_row04_traceSegment_044_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 135 13 14, g32p_row04_traceSegment_044_0135_0013, g32p_row04_traceSegment_044_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 108 27 27, g32p_row04_traceSegment_044_0108_0027, g32p_row04_traceSegment_044_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 162 13 14, g32p_row04_traceSegment_044_0162_0013, g32p_row04_traceSegment_044_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 189 13 14, g32p_row04_traceSegment_044_0189_0013, g32p_row04_traceSegment_044_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 162 27 27, g32p_row04_traceSegment_044_0162_0027, g32p_row04_traceSegment_044_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 108 54 54, g32p_row04_traceSegment_044_0108_0054, g32p_row04_traceSegment_044_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 108 108, g32p_row04_traceSegment_044_0000_0108, g32p_row04_traceSegment_044_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 216 13 14, g32p_row04_traceSegment_044_0216_0013, g32p_row04_traceSegment_044_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 243 13 14, g32p_row04_traceSegment_044_0243_0013, g32p_row04_traceSegment_044_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 216 27 27, g32p_row04_traceSegment_044_0216_0027, g32p_row04_traceSegment_044_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 270 13 14, g32p_row04_traceSegment_044_0270_0013, g32p_row04_traceSegment_044_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 297 13 14, g32p_row04_traceSegment_044_0297_0013, g32p_row04_traceSegment_044_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 270 27 27, g32p_row04_traceSegment_044_0270_0027, g32p_row04_traceSegment_044_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 216 54 54, g32p_row04_traceSegment_044_0216_0054, g32p_row04_traceSegment_044_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 324 13 14, g32p_row04_traceSegment_044_0324_0013, g32p_row04_traceSegment_044_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 351 13 14, g32p_row04_traceSegment_044_0351_0013, g32p_row04_traceSegment_044_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 324 27 27, g32p_row04_traceSegment_044_0324_0027, g32p_row04_traceSegment_044_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 378 13 14, g32p_row04_traceSegment_044_0378_0013, g32p_row04_traceSegment_044_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 405 13 14, g32p_row04_traceSegment_044_0405_0013, g32p_row04_traceSegment_044_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 378 27 27, g32p_row04_traceSegment_044_0378_0027, g32p_row04_traceSegment_044_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 324 54 54, g32p_row04_traceSegment_044_0324_0054, g32p_row04_traceSegment_044_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 216 108 108, g32p_row04_traceSegment_044_0216_0108, g32p_row04_traceSegment_044_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_044 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 216 216, g32p_row04_traceSegment_044_0000_0216, g32p_row04_traceSegment_044_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 432 13 14, g32p_row04_traceSegment_044_0432_0013, g32p_row04_traceSegment_044_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 459 13 14, g32p_row04_traceSegment_044_0459_0013, g32p_row04_traceSegment_044_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 432 27 27, g32p_row04_traceSegment_044_0432_0027, g32p_row04_traceSegment_044_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 486 13 14, g32p_row04_traceSegment_044_0486_0013, g32p_row04_traceSegment_044_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 513 13 14, g32p_row04_traceSegment_044_0513_0013, g32p_row04_traceSegment_044_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 486 27 27, g32p_row04_traceSegment_044_0486_0027, g32p_row04_traceSegment_044_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 432 54 54, g32p_row04_traceSegment_044_0432_0054, g32p_row04_traceSegment_044_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 540 13 14, g32p_row04_traceSegment_044_0540_0013, g32p_row04_traceSegment_044_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 567 13 14, g32p_row04_traceSegment_044_0567_0013, g32p_row04_traceSegment_044_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 540 27 27, g32p_row04_traceSegment_044_0540_0027, g32p_row04_traceSegment_044_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 594 13 14, g32p_row04_traceSegment_044_0594_0013, g32p_row04_traceSegment_044_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 621 13 14, g32p_row04_traceSegment_044_0621_0013, g32p_row04_traceSegment_044_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 594 27 27, g32p_row04_traceSegment_044_0594_0027, g32p_row04_traceSegment_044_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 540 54 54, g32p_row04_traceSegment_044_0540_0054, g32p_row04_traceSegment_044_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 432 108 108, g32p_row04_traceSegment_044_0432_0108, g32p_row04_traceSegment_044_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 648 13 14, g32p_row04_traceSegment_044_0648_0013, g32p_row04_traceSegment_044_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 675 13 14, g32p_row04_traceSegment_044_0675_0013, g32p_row04_traceSegment_044_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 648 27 27, g32p_row04_traceSegment_044_0648_0027, g32p_row04_traceSegment_044_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 702 13 14, g32p_row04_traceSegment_044_0702_0013, g32p_row04_traceSegment_044_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 729 13 14, g32p_row04_traceSegment_044_0729_0013, g32p_row04_traceSegment_044_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 702 27 27, g32p_row04_traceSegment_044_0702_0027, g32p_row04_traceSegment_044_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 648 54 54, g32p_row04_traceSegment_044_0648_0054, g32p_row04_traceSegment_044_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 756 13 14, g32p_row04_traceSegment_044_0756_0013, g32p_row04_traceSegment_044_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 783 13 14, g32p_row04_traceSegment_044_0783_0013, g32p_row04_traceSegment_044_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 756 27 27, g32p_row04_traceSegment_044_0756_0027, g32p_row04_traceSegment_044_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 810 13 14, g32p_row04_traceSegment_044_0810_0013, g32p_row04_traceSegment_044_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 837 13 14, g32p_row04_traceSegment_044_0837_0013, g32p_row04_traceSegment_044_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 810 27 27, g32p_row04_traceSegment_044_0810_0027, g32p_row04_traceSegment_044_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 756 54 54, g32p_row04_traceSegment_044_0756_0054, g32p_row04_traceSegment_044_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 648 108 108, g32p_row04_traceSegment_044_0648_0108, g32p_row04_traceSegment_044_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_044 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 432 216 216, g32p_row04_traceSegment_044_0432_0216, g32p_row04_traceSegment_044_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_044 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 432 432, g32p_row04_traceSegment_044_0000_0432, g32p_row04_traceSegment_044_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 864 13 14, g32p_row04_traceSegment_044_0864_0013, g32p_row04_traceSegment_044_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 891 13 14, g32p_row04_traceSegment_044_0891_0013, g32p_row04_traceSegment_044_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 864 27 27, g32p_row04_traceSegment_044_0864_0027, g32p_row04_traceSegment_044_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 918 13 14, g32p_row04_traceSegment_044_0918_0013, g32p_row04_traceSegment_044_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 945 13 14, g32p_row04_traceSegment_044_0945_0013, g32p_row04_traceSegment_044_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 918 27 27, g32p_row04_traceSegment_044_0918_0027, g32p_row04_traceSegment_044_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 864 54 54, g32p_row04_traceSegment_044_0864_0054, g32p_row04_traceSegment_044_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 972 13 14, g32p_row04_traceSegment_044_0972_0013, g32p_row04_traceSegment_044_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 999 13 14, g32p_row04_traceSegment_044_0999_0013, g32p_row04_traceSegment_044_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 972 27 27, g32p_row04_traceSegment_044_0972_0027, g32p_row04_traceSegment_044_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1026 13 14, g32p_row04_traceSegment_044_1026_0013, g32p_row04_traceSegment_044_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1053 13 14, g32p_row04_traceSegment_044_1053_0013, g32p_row04_traceSegment_044_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1026 27 27, g32p_row04_traceSegment_044_1026_0027, g32p_row04_traceSegment_044_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 972 54 54, g32p_row04_traceSegment_044_0972_0054, g32p_row04_traceSegment_044_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 864 108 108, g32p_row04_traceSegment_044_0864_0108, g32p_row04_traceSegment_044_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1080 13 14, g32p_row04_traceSegment_044_1080_0013, g32p_row04_traceSegment_044_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1107 13 14, g32p_row04_traceSegment_044_1107_0013, g32p_row04_traceSegment_044_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1080 27 27, g32p_row04_traceSegment_044_1080_0027, g32p_row04_traceSegment_044_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1134 13 14, g32p_row04_traceSegment_044_1134_0013, g32p_row04_traceSegment_044_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1161 13 14, g32p_row04_traceSegment_044_1161_0013, g32p_row04_traceSegment_044_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1134 27 27, g32p_row04_traceSegment_044_1134_0027, g32p_row04_traceSegment_044_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1080 54 54, g32p_row04_traceSegment_044_1080_0054, g32p_row04_traceSegment_044_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1188 13 14, g32p_row04_traceSegment_044_1188_0013, g32p_row04_traceSegment_044_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1215 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1215 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1215 13 14, g32p_row04_traceSegment_044_1215_0013, g32p_row04_traceSegment_044_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1188 27 27, g32p_row04_traceSegment_044_1188_0027, g32p_row04_traceSegment_044_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1242 13 14, g32p_row04_traceSegment_044_1242_0013, g32p_row04_traceSegment_044_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1269 13 14, g32p_row04_traceSegment_044_1269_0013, g32p_row04_traceSegment_044_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1242 27 27, g32p_row04_traceSegment_044_1242_0027, g32p_row04_traceSegment_044_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 1188 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1188 54 54, g32p_row04_traceSegment_044_1188_0054, g32p_row04_traceSegment_044_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1080 108 108, g32p_row04_traceSegment_044_1080_0108, g32p_row04_traceSegment_044_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_044 864 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 864 216 216, g32p_row04_traceSegment_044_0864_0216, g32p_row04_traceSegment_044_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1296 13 14, g32p_row04_traceSegment_044_1296_0013, g32p_row04_traceSegment_044_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1323 13 14, g32p_row04_traceSegment_044_1323_0013, g32p_row04_traceSegment_044_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1296 27 27, g32p_row04_traceSegment_044_1296_0027, g32p_row04_traceSegment_044_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1350 13 14, g32p_row04_traceSegment_044_1350_0013, g32p_row04_traceSegment_044_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1377 13 14, g32p_row04_traceSegment_044_1377_0013, g32p_row04_traceSegment_044_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1350 27 27, g32p_row04_traceSegment_044_1350_0027, g32p_row04_traceSegment_044_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1296 54 54, g32p_row04_traceSegment_044_1296_0054, g32p_row04_traceSegment_044_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1404 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1417 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1404 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1404 13 14, g32p_row04_traceSegment_044_1404_0013, g32p_row04_traceSegment_044_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1444 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1431 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1431 13 14, g32p_row04_traceSegment_044_1431_0013, g32p_row04_traceSegment_044_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1404 54 = [4, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1404 27 27, g32p_row04_traceSegment_044_1404_0027, g32p_row04_traceSegment_044_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1471 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1458 13 14, g32p_row04_traceSegment_044_1458_0013, g32p_row04_traceSegment_044_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1485 13 14, g32p_row04_traceSegment_044_1485_0013, g32p_row04_traceSegment_044_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1458 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1458 27 27, g32p_row04_traceSegment_044_1458_0027, g32p_row04_traceSegment_044_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 1404 108 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1404 54 54, g32p_row04_traceSegment_044_1404_0054, g32p_row04_traceSegment_044_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 1296 216 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1296 108 108, g32p_row04_traceSegment_044_1296_0108, g32p_row04_traceSegment_044_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1512 13 14, g32p_row04_traceSegment_044_1512_0013, g32p_row04_traceSegment_044_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1539 13 14, g32p_row04_traceSegment_044_1539_0013, g32p_row04_traceSegment_044_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1512 27 27, g32p_row04_traceSegment_044_1512_0027, g32p_row04_traceSegment_044_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1566 13 14, g32p_row04_traceSegment_044_1566_0013, g32p_row04_traceSegment_044_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1593 13 14, g32p_row04_traceSegment_044_1593_0013, g32p_row04_traceSegment_044_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1566 27 27, g32p_row04_traceSegment_044_1566_0027, g32p_row04_traceSegment_044_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1512 54 54, g32p_row04_traceSegment_044_1512_0054, g32p_row04_traceSegment_044_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1620 13 14, g32p_row04_traceSegment_044_1620_0013, g32p_row04_traceSegment_044_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1647 13 14, g32p_row04_traceSegment_044_1647_0013, g32p_row04_traceSegment_044_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1620 27 27, g32p_row04_traceSegment_044_1620_0027, g32p_row04_traceSegment_044_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1674 13 14, g32p_row04_traceSegment_044_1674_0013, g32p_row04_traceSegment_044_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_044 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_044 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_044_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_044 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1701 13 14, g32p_row04_traceSegment_044_1701_0013, g32p_row04_traceSegment_044_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_044 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1674 27 27, g32p_row04_traceSegment_044_1674_0027, g32p_row04_traceSegment_044_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_044 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1620 54 54, g32p_row04_traceSegment_044_1620_0054, g32p_row04_traceSegment_044_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_044 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1512 108 108, g32p_row04_traceSegment_044_1512_0108, g32p_row04_traceSegment_044_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_044_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_044 1296 432 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 1296 216 216, g32p_row04_traceSegment_044_1296_0216, g32p_row04_traceSegment_044_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_044 864 864 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 864 432 432, g32p_row04_traceSegment_044_0864_0432, g32p_row04_traceSegment_044_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_044_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_044 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_044 0 864 864, g32p_row04_traceSegment_044_0000_0864, g32p_row04_traceSegment_044_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 44 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_044_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 32) (g32p_literalTraceValue 3 32)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_032]
  decide +kernel

theorem g32p_row04_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 34) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 34) (g32p_literalTraceValue 3 34)
      [1, 1, 1] [10368] = true := by
  rw [g32p_row04_traceCoefficients_034]
  decide +kernel

theorem g32p_row04_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 35) (g32p_literalTraceValue 3 35)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_035]
  decide +kernel

theorem g32p_row04_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 37) (g32p_literalTraceValue 3 37)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row04_traceCoefficients_037]
  decide +kernel

theorem g32p_row04_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 40) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 40) (g32p_literalTraceValue 3 40)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_040]
  decide +kernel

theorem g32p_row04_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 41) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 41) (g32p_literalTraceValue 3 41)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_041]
  decide +kernel

theorem g32p_row04_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 43) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 43) (g32p_literalTraceValue 3 43)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_043]
  decide +kernel

theorem g32p_row04_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 44) (g32p_literalTraceValue 3 44)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_044]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
