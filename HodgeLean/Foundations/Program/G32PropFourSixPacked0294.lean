import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_008 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 8 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_008_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 13 14, g32p_row02_traceSegment_008_0000_0013, g32p_row02_traceSegment_008_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 27 13 14, g32p_row02_traceSegment_008_0027_0013, g32p_row02_traceSegment_008_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 27 27, g32p_row02_traceSegment_008_0000_0027, g32p_row02_traceSegment_008_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 54 13 14, g32p_row02_traceSegment_008_0054_0013, g32p_row02_traceSegment_008_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 81 13 14, g32p_row02_traceSegment_008_0081_0013, g32p_row02_traceSegment_008_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 54 27 27, g32p_row02_traceSegment_008_0054_0027, g32p_row02_traceSegment_008_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 54 54, g32p_row02_traceSegment_008_0000_0054, g32p_row02_traceSegment_008_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 108 13 14, g32p_row02_traceSegment_008_0108_0013, g32p_row02_traceSegment_008_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 135 13 14, g32p_row02_traceSegment_008_0135_0013, g32p_row02_traceSegment_008_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 108 27 27, g32p_row02_traceSegment_008_0108_0027, g32p_row02_traceSegment_008_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 162 13 14, g32p_row02_traceSegment_008_0162_0013, g32p_row02_traceSegment_008_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 189 13 14, g32p_row02_traceSegment_008_0189_0013, g32p_row02_traceSegment_008_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 162 27 27, g32p_row02_traceSegment_008_0162_0027, g32p_row02_traceSegment_008_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 108 54 54, g32p_row02_traceSegment_008_0108_0054, g32p_row02_traceSegment_008_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 108 108, g32p_row02_traceSegment_008_0000_0108, g32p_row02_traceSegment_008_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 216 13 14, g32p_row02_traceSegment_008_0216_0013, g32p_row02_traceSegment_008_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 243 13 14, g32p_row02_traceSegment_008_0243_0013, g32p_row02_traceSegment_008_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 216 27 27, g32p_row02_traceSegment_008_0216_0027, g32p_row02_traceSegment_008_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 270 13 14, g32p_row02_traceSegment_008_0270_0013, g32p_row02_traceSegment_008_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 297 13 14, g32p_row02_traceSegment_008_0297_0013, g32p_row02_traceSegment_008_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 270 27 27, g32p_row02_traceSegment_008_0270_0027, g32p_row02_traceSegment_008_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 216 54 54, g32p_row02_traceSegment_008_0216_0054, g32p_row02_traceSegment_008_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 324 13 14, g32p_row02_traceSegment_008_0324_0013, g32p_row02_traceSegment_008_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 351 13 14, g32p_row02_traceSegment_008_0351_0013, g32p_row02_traceSegment_008_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 324 27 27, g32p_row02_traceSegment_008_0324_0027, g32p_row02_traceSegment_008_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 378 13 14, g32p_row02_traceSegment_008_0378_0013, g32p_row02_traceSegment_008_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 405 13 14, g32p_row02_traceSegment_008_0405_0013, g32p_row02_traceSegment_008_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 378 27 27, g32p_row02_traceSegment_008_0378_0027, g32p_row02_traceSegment_008_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 324 54 54, g32p_row02_traceSegment_008_0324_0054, g32p_row02_traceSegment_008_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 216 108 108, g32p_row02_traceSegment_008_0216_0108, g32p_row02_traceSegment_008_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 216 216, g32p_row02_traceSegment_008_0000_0216, g32p_row02_traceSegment_008_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 432 13 14, g32p_row02_traceSegment_008_0432_0013, g32p_row02_traceSegment_008_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 459 13 14, g32p_row02_traceSegment_008_0459_0013, g32p_row02_traceSegment_008_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 432 27 27, g32p_row02_traceSegment_008_0432_0027, g32p_row02_traceSegment_008_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 486 13 14, g32p_row02_traceSegment_008_0486_0013, g32p_row02_traceSegment_008_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 513 13 14, g32p_row02_traceSegment_008_0513_0013, g32p_row02_traceSegment_008_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 486 27 27, g32p_row02_traceSegment_008_0486_0027, g32p_row02_traceSegment_008_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 432 54 54, g32p_row02_traceSegment_008_0432_0054, g32p_row02_traceSegment_008_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 540 13 14, g32p_row02_traceSegment_008_0540_0013, g32p_row02_traceSegment_008_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 567 13 14, g32p_row02_traceSegment_008_0567_0013, g32p_row02_traceSegment_008_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 540 27 27, g32p_row02_traceSegment_008_0540_0027, g32p_row02_traceSegment_008_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 594 13 14, g32p_row02_traceSegment_008_0594_0013, g32p_row02_traceSegment_008_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 621 13 14, g32p_row02_traceSegment_008_0621_0013, g32p_row02_traceSegment_008_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 594 27 27, g32p_row02_traceSegment_008_0594_0027, g32p_row02_traceSegment_008_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 540 54 54, g32p_row02_traceSegment_008_0540_0054, g32p_row02_traceSegment_008_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 432 108 108, g32p_row02_traceSegment_008_0432_0108, g32p_row02_traceSegment_008_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 648 13 14, g32p_row02_traceSegment_008_0648_0013, g32p_row02_traceSegment_008_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 675 13 14, g32p_row02_traceSegment_008_0675_0013, g32p_row02_traceSegment_008_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 648 27 27, g32p_row02_traceSegment_008_0648_0027, g32p_row02_traceSegment_008_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 702 13 14, g32p_row02_traceSegment_008_0702_0013, g32p_row02_traceSegment_008_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 729 13 14, g32p_row02_traceSegment_008_0729_0013, g32p_row02_traceSegment_008_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 702 27 27, g32p_row02_traceSegment_008_0702_0027, g32p_row02_traceSegment_008_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 648 54 54, g32p_row02_traceSegment_008_0648_0054, g32p_row02_traceSegment_008_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 756 13 14, g32p_row02_traceSegment_008_0756_0013, g32p_row02_traceSegment_008_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 783 13 14, g32p_row02_traceSegment_008_0783_0013, g32p_row02_traceSegment_008_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 756 27 27, g32p_row02_traceSegment_008_0756_0027, g32p_row02_traceSegment_008_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 810 13 14, g32p_row02_traceSegment_008_0810_0013, g32p_row02_traceSegment_008_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 837 13 14, g32p_row02_traceSegment_008_0837_0013, g32p_row02_traceSegment_008_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 810 27 27, g32p_row02_traceSegment_008_0810_0027, g32p_row02_traceSegment_008_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 756 54 54, g32p_row02_traceSegment_008_0756_0054, g32p_row02_traceSegment_008_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 648 108 108, g32p_row02_traceSegment_008_0648_0108, g32p_row02_traceSegment_008_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 432 216 216, g32p_row02_traceSegment_008_0432_0216, g32p_row02_traceSegment_008_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_008 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 432 432, g32p_row02_traceSegment_008_0000_0432, g32p_row02_traceSegment_008_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 864 13 14, g32p_row02_traceSegment_008_0864_0013, g32p_row02_traceSegment_008_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 891 13 14, g32p_row02_traceSegment_008_0891_0013, g32p_row02_traceSegment_008_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 864 27 27, g32p_row02_traceSegment_008_0864_0027, g32p_row02_traceSegment_008_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 918 13 14, g32p_row02_traceSegment_008_0918_0013, g32p_row02_traceSegment_008_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 945 13 14, g32p_row02_traceSegment_008_0945_0013, g32p_row02_traceSegment_008_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 918 27 27, g32p_row02_traceSegment_008_0918_0027, g32p_row02_traceSegment_008_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 864 54 54, g32p_row02_traceSegment_008_0864_0054, g32p_row02_traceSegment_008_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 972 13 14, g32p_row02_traceSegment_008_0972_0013, g32p_row02_traceSegment_008_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 999 13 14, g32p_row02_traceSegment_008_0999_0013, g32p_row02_traceSegment_008_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 972 27 27, g32p_row02_traceSegment_008_0972_0027, g32p_row02_traceSegment_008_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1026 13 14, g32p_row02_traceSegment_008_1026_0013, g32p_row02_traceSegment_008_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1053 13 14, g32p_row02_traceSegment_008_1053_0013, g32p_row02_traceSegment_008_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1026 27 27, g32p_row02_traceSegment_008_1026_0027, g32p_row02_traceSegment_008_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 972 54 54, g32p_row02_traceSegment_008_0972_0054, g32p_row02_traceSegment_008_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 864 108 108, g32p_row02_traceSegment_008_0864_0108, g32p_row02_traceSegment_008_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1080 13 14, g32p_row02_traceSegment_008_1080_0013, g32p_row02_traceSegment_008_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1107 13 14, g32p_row02_traceSegment_008_1107_0013, g32p_row02_traceSegment_008_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1080 27 27, g32p_row02_traceSegment_008_1080_0027, g32p_row02_traceSegment_008_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1134 13 14, g32p_row02_traceSegment_008_1134_0013, g32p_row02_traceSegment_008_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1161 13 14, g32p_row02_traceSegment_008_1161_0013, g32p_row02_traceSegment_008_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1134 27 27, g32p_row02_traceSegment_008_1134_0027, g32p_row02_traceSegment_008_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1080 54 54, g32p_row02_traceSegment_008_1080_0054, g32p_row02_traceSegment_008_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1188 13 14, g32p_row02_traceSegment_008_1188_0013, g32p_row02_traceSegment_008_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1215 13 14, g32p_row02_traceSegment_008_1215_0013, g32p_row02_traceSegment_008_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1188 27 27, g32p_row02_traceSegment_008_1188_0027, g32p_row02_traceSegment_008_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1242 13 14, g32p_row02_traceSegment_008_1242_0013, g32p_row02_traceSegment_008_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1269 13 14, g32p_row02_traceSegment_008_1269_0013, g32p_row02_traceSegment_008_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1242 27 27, g32p_row02_traceSegment_008_1242_0027, g32p_row02_traceSegment_008_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1188 54 54, g32p_row02_traceSegment_008_1188_0054, g32p_row02_traceSegment_008_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1080 108 108, g32p_row02_traceSegment_008_1080_0108, g32p_row02_traceSegment_008_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 864 216 216, g32p_row02_traceSegment_008_0864_0216, g32p_row02_traceSegment_008_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1296 13 14, g32p_row02_traceSegment_008_1296_0013, g32p_row02_traceSegment_008_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1323 13 14, g32p_row02_traceSegment_008_1323_0013, g32p_row02_traceSegment_008_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1296 27 27, g32p_row02_traceSegment_008_1296_0027, g32p_row02_traceSegment_008_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1350 13 14, g32p_row02_traceSegment_008_1350_0013, g32p_row02_traceSegment_008_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1377 13 14, g32p_row02_traceSegment_008_1377_0013, g32p_row02_traceSegment_008_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1350 27 27, g32p_row02_traceSegment_008_1350_0027, g32p_row02_traceSegment_008_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1296 54 54, g32p_row02_traceSegment_008_1296_0054, g32p_row02_traceSegment_008_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1404 13 14, g32p_row02_traceSegment_008_1404_0013, g32p_row02_traceSegment_008_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1431 13 14, g32p_row02_traceSegment_008_1431_0013, g32p_row02_traceSegment_008_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1404 27 27, g32p_row02_traceSegment_008_1404_0027, g32p_row02_traceSegment_008_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1458 13 14, g32p_row02_traceSegment_008_1458_0013, g32p_row02_traceSegment_008_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1485 13 14, g32p_row02_traceSegment_008_1485_0013, g32p_row02_traceSegment_008_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1458 27 27, g32p_row02_traceSegment_008_1458_0027, g32p_row02_traceSegment_008_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1404 54 54, g32p_row02_traceSegment_008_1404_0054, g32p_row02_traceSegment_008_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1296 108 108, g32p_row02_traceSegment_008_1296_0108, g32p_row02_traceSegment_008_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1512 13 14, g32p_row02_traceSegment_008_1512_0013, g32p_row02_traceSegment_008_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1552 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1539 13 14, g32p_row02_traceSegment_008_1539_0013, g32p_row02_traceSegment_008_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1512 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1512 27 27, g32p_row02_traceSegment_008_1512_0027, g32p_row02_traceSegment_008_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1566 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1566 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1566 13 14, g32p_row02_traceSegment_008_1566_0013, g32p_row02_traceSegment_008_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1606 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1593 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1593 13 14, g32p_row02_traceSegment_008_1593_0013, g32p_row02_traceSegment_008_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1566 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1566 27 27, g32p_row02_traceSegment_008_1566_0027, g32p_row02_traceSegment_008_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1512 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1512 54 54, g32p_row02_traceSegment_008_1512_0054, g32p_row02_traceSegment_008_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1620 13 14, g32p_row02_traceSegment_008_1620_0013, g32p_row02_traceSegment_008_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1647 13 14, g32p_row02_traceSegment_008_1647_0013, g32p_row02_traceSegment_008_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1620 27 27, g32p_row02_traceSegment_008_1620_0027, g32p_row02_traceSegment_008_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1674 13 14, g32p_row02_traceSegment_008_1674_0013, g32p_row02_traceSegment_008_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1701 13 14, g32p_row02_traceSegment_008_1701_0013, g32p_row02_traceSegment_008_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1674 27 27, g32p_row02_traceSegment_008_1674_0027, g32p_row02_traceSegment_008_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1620 54 54, g32p_row02_traceSegment_008_1620_0054, g32p_row02_traceSegment_008_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1512 108 108, g32p_row02_traceSegment_008_1512_0108, g32p_row02_traceSegment_008_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1296 216 216, g32p_row02_traceSegment_008_1296_0216, g32p_row02_traceSegment_008_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_008 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 864 432 432, g32p_row02_traceSegment_008_0864_0432, g32p_row02_traceSegment_008_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_008 0 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 864 864, g32p_row02_traceSegment_008_0000_0864, g32p_row02_traceSegment_008_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 13 14, g32p_row02_traceSegment_008_1728_0013, g32p_row02_traceSegment_008_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1768 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1755 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1755 13 14, g32p_row02_traceSegment_008_1755_0013, g32p_row02_traceSegment_008_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 27 27, g32p_row02_traceSegment_008_1728_0027, g32p_row02_traceSegment_008_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1795 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1782 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1782 13 14, g32p_row02_traceSegment_008_1782_0013, g32p_row02_traceSegment_008_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1809 13 14, g32p_row02_traceSegment_008_1809_0013, g32p_row02_traceSegment_008_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1782 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1782 27 27, g32p_row02_traceSegment_008_1782_0027, g32p_row02_traceSegment_008_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 54 54, g32p_row02_traceSegment_008_1728_0054, g32p_row02_traceSegment_008_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1836 13 14, g32p_row02_traceSegment_008_1836_0013, g32p_row02_traceSegment_008_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1863 13 14, g32p_row02_traceSegment_008_1863_0013, g32p_row02_traceSegment_008_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1836 27 27, g32p_row02_traceSegment_008_1836_0027, g32p_row02_traceSegment_008_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1890 13 14, g32p_row02_traceSegment_008_1890_0013, g32p_row02_traceSegment_008_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1917 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1917 13 14, g32p_row02_traceSegment_008_1917_0013, g32p_row02_traceSegment_008_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1890 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1890 27 27, g32p_row02_traceSegment_008_1890_0027, g32p_row02_traceSegment_008_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1836 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1836 54 54, g32p_row02_traceSegment_008_1836_0054, g32p_row02_traceSegment_008_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 108 108, g32p_row02_traceSegment_008_1728_0108, g32p_row02_traceSegment_008_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1944 13 14, g32p_row02_traceSegment_008_1944_0013, g32p_row02_traceSegment_008_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1971 13 14, g32p_row02_traceSegment_008_1971_0013, g32p_row02_traceSegment_008_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1944 27 27, g32p_row02_traceSegment_008_1944_0027, g32p_row02_traceSegment_008_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1998 13 14, g32p_row02_traceSegment_008_1998_0013, g32p_row02_traceSegment_008_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2025 13 14, g32p_row02_traceSegment_008_2025_0013, g32p_row02_traceSegment_008_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1998 27 27, g32p_row02_traceSegment_008_1998_0027, g32p_row02_traceSegment_008_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1944 54 54, g32p_row02_traceSegment_008_1944_0054, g32p_row02_traceSegment_008_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2052 13 14, g32p_row02_traceSegment_008_2052_0013, g32p_row02_traceSegment_008_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2079 13 14, g32p_row02_traceSegment_008_2079_0013, g32p_row02_traceSegment_008_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2052 27 27, g32p_row02_traceSegment_008_2052_0027, g32p_row02_traceSegment_008_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2106 13 14, g32p_row02_traceSegment_008_2106_0013, g32p_row02_traceSegment_008_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2133 13 14, g32p_row02_traceSegment_008_2133_0013, g32p_row02_traceSegment_008_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2106 27 27, g32p_row02_traceSegment_008_2106_0027, g32p_row02_traceSegment_008_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2052 54 54, g32p_row02_traceSegment_008_2052_0054, g32p_row02_traceSegment_008_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1944 108 108, g32p_row02_traceSegment_008_1944_0108, g32p_row02_traceSegment_008_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 216 216, g32p_row02_traceSegment_008_1728_0216, g32p_row02_traceSegment_008_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2160 13 14, g32p_row02_traceSegment_008_2160_0013, g32p_row02_traceSegment_008_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2187 13 14, g32p_row02_traceSegment_008_2187_0013, g32p_row02_traceSegment_008_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2160 27 27, g32p_row02_traceSegment_008_2160_0027, g32p_row02_traceSegment_008_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2227 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2214 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2214 13 14, g32p_row02_traceSegment_008_2214_0013, g32p_row02_traceSegment_008_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2241 13 14, g32p_row02_traceSegment_008_2241_0013, g32p_row02_traceSegment_008_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2214 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2214 27 27, g32p_row02_traceSegment_008_2214_0027, g32p_row02_traceSegment_008_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2160 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2160 54 54, g32p_row02_traceSegment_008_2160_0054, g32p_row02_traceSegment_008_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2268 13 14, g32p_row02_traceSegment_008_2268_0013, g32p_row02_traceSegment_008_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2295 13 14, g32p_row02_traceSegment_008_2295_0013, g32p_row02_traceSegment_008_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2268 27 27, g32p_row02_traceSegment_008_2268_0027, g32p_row02_traceSegment_008_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2322 13 14, g32p_row02_traceSegment_008_2322_0013, g32p_row02_traceSegment_008_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2349 13 14, g32p_row02_traceSegment_008_2349_0013, g32p_row02_traceSegment_008_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2322 27 27, g32p_row02_traceSegment_008_2322_0027, g32p_row02_traceSegment_008_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2268 54 54, g32p_row02_traceSegment_008_2268_0054, g32p_row02_traceSegment_008_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 2160 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2160 108 108, g32p_row02_traceSegment_008_2160_0108, g32p_row02_traceSegment_008_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2376 13 14, g32p_row02_traceSegment_008_2376_0013, g32p_row02_traceSegment_008_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2403 13 14, g32p_row02_traceSegment_008_2403_0013, g32p_row02_traceSegment_008_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2376 27 27, g32p_row02_traceSegment_008_2376_0027, g32p_row02_traceSegment_008_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2430 13 14, g32p_row02_traceSegment_008_2430_0013, g32p_row02_traceSegment_008_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2457 13 14, g32p_row02_traceSegment_008_2457_0013, g32p_row02_traceSegment_008_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2430 27 27, g32p_row02_traceSegment_008_2430_0027, g32p_row02_traceSegment_008_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2376 54 54, g32p_row02_traceSegment_008_2376_0054, g32p_row02_traceSegment_008_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2484 13 14, g32p_row02_traceSegment_008_2484_0013, g32p_row02_traceSegment_008_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2511 13 14, g32p_row02_traceSegment_008_2511_0013, g32p_row02_traceSegment_008_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2484 27 27, g32p_row02_traceSegment_008_2484_0027, g32p_row02_traceSegment_008_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2538 13 14, g32p_row02_traceSegment_008_2538_0013, g32p_row02_traceSegment_008_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2565 13 14, g32p_row02_traceSegment_008_2565_0013, g32p_row02_traceSegment_008_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2538 27 27, g32p_row02_traceSegment_008_2538_0027, g32p_row02_traceSegment_008_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2484 54 54, g32p_row02_traceSegment_008_2484_0054, g32p_row02_traceSegment_008_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2376 108 108, g32p_row02_traceSegment_008_2376_0108, g32p_row02_traceSegment_008_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 2160 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2160 216 216, g32p_row02_traceSegment_008_2160_0216, g32p_row02_traceSegment_008_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 432 432, g32p_row02_traceSegment_008_1728_0432, g32p_row02_traceSegment_008_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2592 13 14, g32p_row02_traceSegment_008_2592_0013, g32p_row02_traceSegment_008_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2619 13 14, g32p_row02_traceSegment_008_2619_0013, g32p_row02_traceSegment_008_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2592 27 27, g32p_row02_traceSegment_008_2592_0027, g32p_row02_traceSegment_008_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2646 13 14, g32p_row02_traceSegment_008_2646_0013, g32p_row02_traceSegment_008_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2673 13 14, g32p_row02_traceSegment_008_2673_0013, g32p_row02_traceSegment_008_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2646 27 27, g32p_row02_traceSegment_008_2646_0027, g32p_row02_traceSegment_008_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2592 54 54, g32p_row02_traceSegment_008_2592_0054, g32p_row02_traceSegment_008_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2700 13 14, g32p_row02_traceSegment_008_2700_0013, g32p_row02_traceSegment_008_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2727 13 14, g32p_row02_traceSegment_008_2727_0013, g32p_row02_traceSegment_008_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2700 27 27, g32p_row02_traceSegment_008_2700_0027, g32p_row02_traceSegment_008_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2754 13 14, g32p_row02_traceSegment_008_2754_0013, g32p_row02_traceSegment_008_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2781 13 14, g32p_row02_traceSegment_008_2781_0013, g32p_row02_traceSegment_008_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2754 27 27, g32p_row02_traceSegment_008_2754_0027, g32p_row02_traceSegment_008_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2700 54 54, g32p_row02_traceSegment_008_2700_0054, g32p_row02_traceSegment_008_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2592 108 108, g32p_row02_traceSegment_008_2592_0108, g32p_row02_traceSegment_008_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2808 13 14, g32p_row02_traceSegment_008_2808_0013, g32p_row02_traceSegment_008_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2835 13 14, g32p_row02_traceSegment_008_2835_0013, g32p_row02_traceSegment_008_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2808 27 27, g32p_row02_traceSegment_008_2808_0027, g32p_row02_traceSegment_008_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2862 13 14, g32p_row02_traceSegment_008_2862_0013, g32p_row02_traceSegment_008_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2889 13 14, g32p_row02_traceSegment_008_2889_0013, g32p_row02_traceSegment_008_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2862 27 27, g32p_row02_traceSegment_008_2862_0027, g32p_row02_traceSegment_008_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2808 54 54, g32p_row02_traceSegment_008_2808_0054, g32p_row02_traceSegment_008_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2916 13 14, g32p_row02_traceSegment_008_2916_0013, g32p_row02_traceSegment_008_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2943 13 14, g32p_row02_traceSegment_008_2943_0013, g32p_row02_traceSegment_008_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2916 27 27, g32p_row02_traceSegment_008_2916_0027, g32p_row02_traceSegment_008_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2970 13 14, g32p_row02_traceSegment_008_2970_0013, g32p_row02_traceSegment_008_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2997 13 14, g32p_row02_traceSegment_008_2997_0013, g32p_row02_traceSegment_008_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2970 27 27, g32p_row02_traceSegment_008_2970_0027, g32p_row02_traceSegment_008_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2916 54 54, g32p_row02_traceSegment_008_2916_0054, g32p_row02_traceSegment_008_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2808 108 108, g32p_row02_traceSegment_008_2808_0108, g32p_row02_traceSegment_008_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2592 216 216, g32p_row02_traceSegment_008_2592_0216, g32p_row02_traceSegment_008_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3024 13 14, g32p_row02_traceSegment_008_3024_0013, g32p_row02_traceSegment_008_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3051 13 14, g32p_row02_traceSegment_008_3051_0013, g32p_row02_traceSegment_008_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3024 27 27, g32p_row02_traceSegment_008_3024_0027, g32p_row02_traceSegment_008_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3078 13 14, g32p_row02_traceSegment_008_3078_0013, g32p_row02_traceSegment_008_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3105 13 14, g32p_row02_traceSegment_008_3105_0013, g32p_row02_traceSegment_008_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3078 27 27, g32p_row02_traceSegment_008_3078_0027, g32p_row02_traceSegment_008_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3024 54 54, g32p_row02_traceSegment_008_3024_0054, g32p_row02_traceSegment_008_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3132 13 14, g32p_row02_traceSegment_008_3132_0013, g32p_row02_traceSegment_008_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3159 13 14, g32p_row02_traceSegment_008_3159_0013, g32p_row02_traceSegment_008_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3132 27 27, g32p_row02_traceSegment_008_3132_0027, g32p_row02_traceSegment_008_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3186 13 14, g32p_row02_traceSegment_008_3186_0013, g32p_row02_traceSegment_008_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3213 13 14, g32p_row02_traceSegment_008_3213_0013, g32p_row02_traceSegment_008_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3186 27 27, g32p_row02_traceSegment_008_3186_0027, g32p_row02_traceSegment_008_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3132 54 54, g32p_row02_traceSegment_008_3132_0054, g32p_row02_traceSegment_008_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3024 108 108, g32p_row02_traceSegment_008_3024_0108, g32p_row02_traceSegment_008_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3240 13 14, g32p_row02_traceSegment_008_3240_0013, g32p_row02_traceSegment_008_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3267 13 14, g32p_row02_traceSegment_008_3267_0013, g32p_row02_traceSegment_008_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3240 27 27, g32p_row02_traceSegment_008_3240_0027, g32p_row02_traceSegment_008_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3294 13 14, g32p_row02_traceSegment_008_3294_0013, g32p_row02_traceSegment_008_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3321 13 14, g32p_row02_traceSegment_008_3321_0013, g32p_row02_traceSegment_008_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3294 27 27, g32p_row02_traceSegment_008_3294_0027, g32p_row02_traceSegment_008_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3240 54 54, g32p_row02_traceSegment_008_3240_0054, g32p_row02_traceSegment_008_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3348 13 14, g32p_row02_traceSegment_008_3348_0013, g32p_row02_traceSegment_008_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3375 13 14, g32p_row02_traceSegment_008_3375_0013, g32p_row02_traceSegment_008_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3348 27 27, g32p_row02_traceSegment_008_3348_0027, g32p_row02_traceSegment_008_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3402 13 14, g32p_row02_traceSegment_008_3402_0013, g32p_row02_traceSegment_008_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_008 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_008 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_008_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_008 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3429 13 14, g32p_row02_traceSegment_008_3429_0013, g32p_row02_traceSegment_008_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_008 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3402 27 27, g32p_row02_traceSegment_008_3402_0027, g32p_row02_traceSegment_008_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_008 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3348 54 54, g32p_row02_traceSegment_008_3348_0054, g32p_row02_traceSegment_008_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_008 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3240 108 108, g32p_row02_traceSegment_008_3240_0108, g32p_row02_traceSegment_008_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_008_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_008 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 3024 216 216, g32p_row02_traceSegment_008_3024_0216, g32p_row02_traceSegment_008_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_008_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_008 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 2592 432 432, g32p_row02_traceSegment_008_2592_0432, g32p_row02_traceSegment_008_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_008_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_008 1728 1728 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 1728 864 864, g32p_row02_traceSegment_008_1728_0864, g32p_row02_traceSegment_008_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_008_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_008 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_008 0 1728 1728, g32p_row02_traceSegment_008_0000_1728, g32p_row02_traceSegment_008_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 8 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_008_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_010 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 10 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_010_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 13 14, g32p_row02_traceSegment_010_0000_0013, g32p_row02_traceSegment_010_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 27 13 14, g32p_row02_traceSegment_010_0027_0013, g32p_row02_traceSegment_010_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 27 27, g32p_row02_traceSegment_010_0000_0027, g32p_row02_traceSegment_010_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 54 13 14, g32p_row02_traceSegment_010_0054_0013, g32p_row02_traceSegment_010_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 81 13 14, g32p_row02_traceSegment_010_0081_0013, g32p_row02_traceSegment_010_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 54 27 27, g32p_row02_traceSegment_010_0054_0027, g32p_row02_traceSegment_010_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 54 54, g32p_row02_traceSegment_010_0000_0054, g32p_row02_traceSegment_010_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 108 13 14, g32p_row02_traceSegment_010_0108_0013, g32p_row02_traceSegment_010_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 135 13 14, g32p_row02_traceSegment_010_0135_0013, g32p_row02_traceSegment_010_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 108 27 27, g32p_row02_traceSegment_010_0108_0027, g32p_row02_traceSegment_010_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 162 13 14, g32p_row02_traceSegment_010_0162_0013, g32p_row02_traceSegment_010_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 189 13 14, g32p_row02_traceSegment_010_0189_0013, g32p_row02_traceSegment_010_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 162 27 27, g32p_row02_traceSegment_010_0162_0027, g32p_row02_traceSegment_010_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 108 54 54, g32p_row02_traceSegment_010_0108_0054, g32p_row02_traceSegment_010_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 108 108, g32p_row02_traceSegment_010_0000_0108, g32p_row02_traceSegment_010_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 216 13 14, g32p_row02_traceSegment_010_0216_0013, g32p_row02_traceSegment_010_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 243 13 14, g32p_row02_traceSegment_010_0243_0013, g32p_row02_traceSegment_010_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 216 27 27, g32p_row02_traceSegment_010_0216_0027, g32p_row02_traceSegment_010_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 270 13 14, g32p_row02_traceSegment_010_0270_0013, g32p_row02_traceSegment_010_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 297 13 14, g32p_row02_traceSegment_010_0297_0013, g32p_row02_traceSegment_010_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 270 27 27, g32p_row02_traceSegment_010_0270_0027, g32p_row02_traceSegment_010_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 216 54 54, g32p_row02_traceSegment_010_0216_0054, g32p_row02_traceSegment_010_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 324 13 14, g32p_row02_traceSegment_010_0324_0013, g32p_row02_traceSegment_010_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 351 13 14, g32p_row02_traceSegment_010_0351_0013, g32p_row02_traceSegment_010_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 324 27 27, g32p_row02_traceSegment_010_0324_0027, g32p_row02_traceSegment_010_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 378 13 14, g32p_row02_traceSegment_010_0378_0013, g32p_row02_traceSegment_010_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 405 13 14, g32p_row02_traceSegment_010_0405_0013, g32p_row02_traceSegment_010_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 378 27 27, g32p_row02_traceSegment_010_0378_0027, g32p_row02_traceSegment_010_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 324 54 54, g32p_row02_traceSegment_010_0324_0054, g32p_row02_traceSegment_010_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 216 108 108, g32p_row02_traceSegment_010_0216_0108, g32p_row02_traceSegment_010_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 216 216, g32p_row02_traceSegment_010_0000_0216, g32p_row02_traceSegment_010_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 432 13 14, g32p_row02_traceSegment_010_0432_0013, g32p_row02_traceSegment_010_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 459 13 14, g32p_row02_traceSegment_010_0459_0013, g32p_row02_traceSegment_010_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 432 27 27, g32p_row02_traceSegment_010_0432_0027, g32p_row02_traceSegment_010_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 486 13 14, g32p_row02_traceSegment_010_0486_0013, g32p_row02_traceSegment_010_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 513 13 14, g32p_row02_traceSegment_010_0513_0013, g32p_row02_traceSegment_010_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 486 27 27, g32p_row02_traceSegment_010_0486_0027, g32p_row02_traceSegment_010_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 432 54 54, g32p_row02_traceSegment_010_0432_0054, g32p_row02_traceSegment_010_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 540 13 14, g32p_row02_traceSegment_010_0540_0013, g32p_row02_traceSegment_010_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 567 13 14, g32p_row02_traceSegment_010_0567_0013, g32p_row02_traceSegment_010_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 540 27 27, g32p_row02_traceSegment_010_0540_0027, g32p_row02_traceSegment_010_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 594 13 14, g32p_row02_traceSegment_010_0594_0013, g32p_row02_traceSegment_010_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 621 13 14, g32p_row02_traceSegment_010_0621_0013, g32p_row02_traceSegment_010_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 594 27 27, g32p_row02_traceSegment_010_0594_0027, g32p_row02_traceSegment_010_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 540 54 54, g32p_row02_traceSegment_010_0540_0054, g32p_row02_traceSegment_010_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 432 108 108, g32p_row02_traceSegment_010_0432_0108, g32p_row02_traceSegment_010_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 648 13 14, g32p_row02_traceSegment_010_0648_0013, g32p_row02_traceSegment_010_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 675 13 14, g32p_row02_traceSegment_010_0675_0013, g32p_row02_traceSegment_010_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 648 27 27, g32p_row02_traceSegment_010_0648_0027, g32p_row02_traceSegment_010_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 702 13 14, g32p_row02_traceSegment_010_0702_0013, g32p_row02_traceSegment_010_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 729 13 14, g32p_row02_traceSegment_010_0729_0013, g32p_row02_traceSegment_010_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 702 27 27, g32p_row02_traceSegment_010_0702_0027, g32p_row02_traceSegment_010_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 648 54 54, g32p_row02_traceSegment_010_0648_0054, g32p_row02_traceSegment_010_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 756 13 14, g32p_row02_traceSegment_010_0756_0013, g32p_row02_traceSegment_010_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 783 13 14, g32p_row02_traceSegment_010_0783_0013, g32p_row02_traceSegment_010_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 756 27 27, g32p_row02_traceSegment_010_0756_0027, g32p_row02_traceSegment_010_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 810 13 14, g32p_row02_traceSegment_010_0810_0013, g32p_row02_traceSegment_010_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 837 13 14, g32p_row02_traceSegment_010_0837_0013, g32p_row02_traceSegment_010_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 810 27 27, g32p_row02_traceSegment_010_0810_0027, g32p_row02_traceSegment_010_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 756 54 54, g32p_row02_traceSegment_010_0756_0054, g32p_row02_traceSegment_010_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 648 108 108, g32p_row02_traceSegment_010_0648_0108, g32p_row02_traceSegment_010_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 432 216 216, g32p_row02_traceSegment_010_0432_0216, g32p_row02_traceSegment_010_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_010 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 432 432, g32p_row02_traceSegment_010_0000_0432, g32p_row02_traceSegment_010_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 864 13 14, g32p_row02_traceSegment_010_0864_0013, g32p_row02_traceSegment_010_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 891 13 14, g32p_row02_traceSegment_010_0891_0013, g32p_row02_traceSegment_010_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 864 27 27, g32p_row02_traceSegment_010_0864_0027, g32p_row02_traceSegment_010_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 918 13 14, g32p_row02_traceSegment_010_0918_0013, g32p_row02_traceSegment_010_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 945 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 958 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 945 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 945 13 14, g32p_row02_traceSegment_010_0945_0013, g32p_row02_traceSegment_010_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 918 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 918 27 27, g32p_row02_traceSegment_010_0918_0027, g32p_row02_traceSegment_010_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 864 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 864 54 54, g32p_row02_traceSegment_010_0864_0054, g32p_row02_traceSegment_010_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 972 13 14, g32p_row02_traceSegment_010_0972_0013, g32p_row02_traceSegment_010_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 999 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 999 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 999 13 14, g32p_row02_traceSegment_010_0999_0013, g32p_row02_traceSegment_010_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 972 27 27, g32p_row02_traceSegment_010_0972_0027, g32p_row02_traceSegment_010_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1026 13 14, g32p_row02_traceSegment_010_1026_0013, g32p_row02_traceSegment_010_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1053 13 14, g32p_row02_traceSegment_010_1053_0013, g32p_row02_traceSegment_010_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1026 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1026 27 27, g32p_row02_traceSegment_010_1026_0027, g32p_row02_traceSegment_010_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 972 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 972 54 54, g32p_row02_traceSegment_010_0972_0054, g32p_row02_traceSegment_010_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 864 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 864 108 108, g32p_row02_traceSegment_010_0864_0108, g32p_row02_traceSegment_010_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1080 13 14, g32p_row02_traceSegment_010_1080_0013, g32p_row02_traceSegment_010_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1107 13 14, g32p_row02_traceSegment_010_1107_0013, g32p_row02_traceSegment_010_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1080 27 27, g32p_row02_traceSegment_010_1080_0027, g32p_row02_traceSegment_010_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1134 13 14, g32p_row02_traceSegment_010_1134_0013, g32p_row02_traceSegment_010_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1174 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1161 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1161 13 14, g32p_row02_traceSegment_010_1161_0013, g32p_row02_traceSegment_010_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1134 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1134 27 27, g32p_row02_traceSegment_010_1134_0027, g32p_row02_traceSegment_010_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1080 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1080 54 54, g32p_row02_traceSegment_010_1080_0054, g32p_row02_traceSegment_010_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1201 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1188 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1188 13 14, g32p_row02_traceSegment_010_1188_0013, g32p_row02_traceSegment_010_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1215 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1215 13 14, g32p_row02_traceSegment_010_1215_0013, g32p_row02_traceSegment_010_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1188 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1188 27 27, g32p_row02_traceSegment_010_1188_0027, g32p_row02_traceSegment_010_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1242 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1242 13 14, g32p_row02_traceSegment_010_1242_0013, g32p_row02_traceSegment_010_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1269 13 14, g32p_row02_traceSegment_010_1269_0013, g32p_row02_traceSegment_010_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1242 27 27, g32p_row02_traceSegment_010_1242_0027, g32p_row02_traceSegment_010_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1188 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1188 54 54, g32p_row02_traceSegment_010_1188_0054, g32p_row02_traceSegment_010_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 1080 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1080 108 108, g32p_row02_traceSegment_010_1080_0108, g32p_row02_traceSegment_010_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 864 432 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 864 216 216, g32p_row02_traceSegment_010_0864_0216, g32p_row02_traceSegment_010_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1296 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1296 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1296 13 14, g32p_row02_traceSegment_010_1296_0013, g32p_row02_traceSegment_010_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1323 13 14, g32p_row02_traceSegment_010_1323_0013, g32p_row02_traceSegment_010_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1296 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1296 27 27, g32p_row02_traceSegment_010_1296_0027, g32p_row02_traceSegment_010_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1350 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1363 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1350 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1350 13 14, g32p_row02_traceSegment_010_1350_0013, g32p_row02_traceSegment_010_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1377 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1377 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1377 13 14, g32p_row02_traceSegment_010_1377_0013, g32p_row02_traceSegment_010_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1350 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1350 27 27, g32p_row02_traceSegment_010_1350_0027, g32p_row02_traceSegment_010_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1296 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1296 54 54, g32p_row02_traceSegment_010_1296_0054, g32p_row02_traceSegment_010_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1404 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1404 13 14, g32p_row02_traceSegment_010_1404_0013, g32p_row02_traceSegment_010_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1431 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1431 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1431 13 14, g32p_row02_traceSegment_010_1431_0013, g32p_row02_traceSegment_010_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1404 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1404 27 27, g32p_row02_traceSegment_010_1404_0027, g32p_row02_traceSegment_010_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1458 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1458 13 14, g32p_row02_traceSegment_010_1458_0013, g32p_row02_traceSegment_010_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1498 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1485 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1485 13 14, g32p_row02_traceSegment_010_1485_0013, g32p_row02_traceSegment_010_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1458 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1458 27 27, g32p_row02_traceSegment_010_1458_0027, g32p_row02_traceSegment_010_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1404 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1404 54 54, g32p_row02_traceSegment_010_1404_0054, g32p_row02_traceSegment_010_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 1296 216 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1296 108 108, g32p_row02_traceSegment_010_1296_0108, g32p_row02_traceSegment_010_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1512 13 14, g32p_row02_traceSegment_010_1512_0013, g32p_row02_traceSegment_010_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1539 13 14, g32p_row02_traceSegment_010_1539_0013, g32p_row02_traceSegment_010_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1512 27 27, g32p_row02_traceSegment_010_1512_0027, g32p_row02_traceSegment_010_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1566 13 14, g32p_row02_traceSegment_010_1566_0013, g32p_row02_traceSegment_010_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1593 13 14, g32p_row02_traceSegment_010_1593_0013, g32p_row02_traceSegment_010_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1566 27 27, g32p_row02_traceSegment_010_1566_0027, g32p_row02_traceSegment_010_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1512 54 54, g32p_row02_traceSegment_010_1512_0054, g32p_row02_traceSegment_010_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1620 13 14, g32p_row02_traceSegment_010_1620_0013, g32p_row02_traceSegment_010_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1647 13 14, g32p_row02_traceSegment_010_1647_0013, g32p_row02_traceSegment_010_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1620 27 27, g32p_row02_traceSegment_010_1620_0027, g32p_row02_traceSegment_010_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1687 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1674 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1674 13 14, g32p_row02_traceSegment_010_1674_0013, g32p_row02_traceSegment_010_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1714 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1701 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1701 13 14, g32p_row02_traceSegment_010_1701_0013, g32p_row02_traceSegment_010_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1674 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1674 27 27, g32p_row02_traceSegment_010_1674_0027, g32p_row02_traceSegment_010_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1620 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1620 54 54, g32p_row02_traceSegment_010_1620_0054, g32p_row02_traceSegment_010_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 1512 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1512 108 108, g32p_row02_traceSegment_010_1512_0108, g32p_row02_traceSegment_010_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 1296 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1296 216 216, g32p_row02_traceSegment_010_1296_0216, g32p_row02_traceSegment_010_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_010 864 864 = [0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 864 432 432, g32p_row02_traceSegment_010_0864_0432, g32p_row02_traceSegment_010_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_010 0 1728 = [0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 864 864, g32p_row02_traceSegment_010_0000_0864, g32p_row02_traceSegment_010_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 13 14, g32p_row02_traceSegment_010_1728_0013, g32p_row02_traceSegment_010_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1755 13 14, g32p_row02_traceSegment_010_1755_0013, g32p_row02_traceSegment_010_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 27 27, g32p_row02_traceSegment_010_1728_0027, g32p_row02_traceSegment_010_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1795 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1782 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1782 13 14, g32p_row02_traceSegment_010_1782_0013, g32p_row02_traceSegment_010_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1809 13 14, g32p_row02_traceSegment_010_1809_0013, g32p_row02_traceSegment_010_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1782 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1782 27 27, g32p_row02_traceSegment_010_1782_0027, g32p_row02_traceSegment_010_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 54 54, g32p_row02_traceSegment_010_1728_0054, g32p_row02_traceSegment_010_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1849 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1836 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1836 13 14, g32p_row02_traceSegment_010_1836_0013, g32p_row02_traceSegment_010_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1863 13 14, g32p_row02_traceSegment_010_1863_0013, g32p_row02_traceSegment_010_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1836 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1836 27 27, g32p_row02_traceSegment_010_1836_0027, g32p_row02_traceSegment_010_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1890 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1890 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1890 13 14, g32p_row02_traceSegment_010_1890_0013, g32p_row02_traceSegment_010_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1917 13 14, g32p_row02_traceSegment_010_1917_0013, g32p_row02_traceSegment_010_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1890 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1890 27 27, g32p_row02_traceSegment_010_1890_0027, g32p_row02_traceSegment_010_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1836 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1836 54 54, g32p_row02_traceSegment_010_1836_0054, g32p_row02_traceSegment_010_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 108 108, g32p_row02_traceSegment_010_1728_0108, g32p_row02_traceSegment_010_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1944 13 14, g32p_row02_traceSegment_010_1944_0013, g32p_row02_traceSegment_010_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1971 13 14, g32p_row02_traceSegment_010_1971_0013, g32p_row02_traceSegment_010_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1944 27 27, g32p_row02_traceSegment_010_1944_0027, g32p_row02_traceSegment_010_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2011 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 1998 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1998 13 14, g32p_row02_traceSegment_010_1998_0013, g32p_row02_traceSegment_010_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2025 13 14, g32p_row02_traceSegment_010_2025_0013, g32p_row02_traceSegment_010_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 1998 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1998 27 27, g32p_row02_traceSegment_010_1998_0027, g32p_row02_traceSegment_010_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 1944 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1944 54 54, g32p_row02_traceSegment_010_1944_0054, g32p_row02_traceSegment_010_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2052 13 14, g32p_row02_traceSegment_010_2052_0013, g32p_row02_traceSegment_010_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2079 13 14, g32p_row02_traceSegment_010_2079_0013, g32p_row02_traceSegment_010_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2052 27 27, g32p_row02_traceSegment_010_2052_0027, g32p_row02_traceSegment_010_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2106 13 14, g32p_row02_traceSegment_010_2106_0013, g32p_row02_traceSegment_010_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2133 13 14, g32p_row02_traceSegment_010_2133_0013, g32p_row02_traceSegment_010_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2106 27 27, g32p_row02_traceSegment_010_2106_0027, g32p_row02_traceSegment_010_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2052 54 54, g32p_row02_traceSegment_010_2052_0054, g32p_row02_traceSegment_010_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 1944 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1944 108 108, g32p_row02_traceSegment_010_1944_0108, g32p_row02_traceSegment_010_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 216 216, g32p_row02_traceSegment_010_1728_0216, g32p_row02_traceSegment_010_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2160 13 14, g32p_row02_traceSegment_010_2160_0013, g32p_row02_traceSegment_010_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2200 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2187 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2187 13 14, g32p_row02_traceSegment_010_2187_0013, g32p_row02_traceSegment_010_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2160 27 27, g32p_row02_traceSegment_010_2160_0027, g32p_row02_traceSegment_010_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2214 13 14, g32p_row02_traceSegment_010_2214_0013, g32p_row02_traceSegment_010_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2241 13 14, g32p_row02_traceSegment_010_2241_0013, g32p_row02_traceSegment_010_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2214 27 27, g32p_row02_traceSegment_010_2214_0027, g32p_row02_traceSegment_010_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2160 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2160 54 54, g32p_row02_traceSegment_010_2160_0054, g32p_row02_traceSegment_010_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2268 13 14, g32p_row02_traceSegment_010_2268_0013, g32p_row02_traceSegment_010_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2295 13 14, g32p_row02_traceSegment_010_2295_0013, g32p_row02_traceSegment_010_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2268 27 27, g32p_row02_traceSegment_010_2268_0027, g32p_row02_traceSegment_010_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2322 13 14, g32p_row02_traceSegment_010_2322_0013, g32p_row02_traceSegment_010_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2349 13 14, g32p_row02_traceSegment_010_2349_0013, g32p_row02_traceSegment_010_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2322 27 27, g32p_row02_traceSegment_010_2322_0027, g32p_row02_traceSegment_010_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2268 54 54, g32p_row02_traceSegment_010_2268_0054, g32p_row02_traceSegment_010_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 2160 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2160 108 108, g32p_row02_traceSegment_010_2160_0108, g32p_row02_traceSegment_010_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2376 13 14, g32p_row02_traceSegment_010_2376_0013, g32p_row02_traceSegment_010_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2403 13 14, g32p_row02_traceSegment_010_2403_0013, g32p_row02_traceSegment_010_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2376 27 27, g32p_row02_traceSegment_010_2376_0027, g32p_row02_traceSegment_010_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2430 13 14, g32p_row02_traceSegment_010_2430_0013, g32p_row02_traceSegment_010_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2457 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2457 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2457 13 14, g32p_row02_traceSegment_010_2457_0013, g32p_row02_traceSegment_010_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2430 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2430 27 27, g32p_row02_traceSegment_010_2430_0027, g32p_row02_traceSegment_010_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2376 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2376 54 54, g32p_row02_traceSegment_010_2376_0054, g32p_row02_traceSegment_010_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2484 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2497 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2484 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2484 13 14, g32p_row02_traceSegment_010_2484_0013, g32p_row02_traceSegment_010_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2511 13 14, g32p_row02_traceSegment_010_2511_0013, g32p_row02_traceSegment_010_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2484 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2484 27 27, g32p_row02_traceSegment_010_2484_0027, g32p_row02_traceSegment_010_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2538 13 14, g32p_row02_traceSegment_010_2538_0013, g32p_row02_traceSegment_010_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2578 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2565 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2565 13 14, g32p_row02_traceSegment_010_2565_0013, g32p_row02_traceSegment_010_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2538 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2538 27 27, g32p_row02_traceSegment_010_2538_0027, g32p_row02_traceSegment_010_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2484 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2484 54 54, g32p_row02_traceSegment_010_2484_0054, g32p_row02_traceSegment_010_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 2376 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2376 108 108, g32p_row02_traceSegment_010_2376_0108, g32p_row02_traceSegment_010_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 2160 432 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2160 216 216, g32p_row02_traceSegment_010_2160_0216, g32p_row02_traceSegment_010_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 864 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 432 432, g32p_row02_traceSegment_010_1728_0432, g32p_row02_traceSegment_010_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2592 13 14, g32p_row02_traceSegment_010_2592_0013, g32p_row02_traceSegment_010_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2619 13 14, g32p_row02_traceSegment_010_2619_0013, g32p_row02_traceSegment_010_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2592 27 27, g32p_row02_traceSegment_010_2592_0027, g32p_row02_traceSegment_010_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2646 13 14, g32p_row02_traceSegment_010_2646_0013, g32p_row02_traceSegment_010_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2673 13 14, g32p_row02_traceSegment_010_2673_0013, g32p_row02_traceSegment_010_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2646 27 27, g32p_row02_traceSegment_010_2646_0027, g32p_row02_traceSegment_010_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2592 54 54, g32p_row02_traceSegment_010_2592_0054, g32p_row02_traceSegment_010_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2700 13 14, g32p_row02_traceSegment_010_2700_0013, g32p_row02_traceSegment_010_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2727 13 14, g32p_row02_traceSegment_010_2727_0013, g32p_row02_traceSegment_010_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2700 27 27, g32p_row02_traceSegment_010_2700_0027, g32p_row02_traceSegment_010_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2754 13 14, g32p_row02_traceSegment_010_2754_0013, g32p_row02_traceSegment_010_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2781 13 14, g32p_row02_traceSegment_010_2781_0013, g32p_row02_traceSegment_010_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2754 27 27, g32p_row02_traceSegment_010_2754_0027, g32p_row02_traceSegment_010_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2700 54 54, g32p_row02_traceSegment_010_2700_0054, g32p_row02_traceSegment_010_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2592 108 108, g32p_row02_traceSegment_010_2592_0108, g32p_row02_traceSegment_010_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2808 13 14, g32p_row02_traceSegment_010_2808_0013, g32p_row02_traceSegment_010_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2835 13 14, g32p_row02_traceSegment_010_2835_0013, g32p_row02_traceSegment_010_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2808 27 27, g32p_row02_traceSegment_010_2808_0027, g32p_row02_traceSegment_010_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2862 13 14, g32p_row02_traceSegment_010_2862_0013, g32p_row02_traceSegment_010_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2889 13 14, g32p_row02_traceSegment_010_2889_0013, g32p_row02_traceSegment_010_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2862 27 27, g32p_row02_traceSegment_010_2862_0027, g32p_row02_traceSegment_010_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2808 54 54, g32p_row02_traceSegment_010_2808_0054, g32p_row02_traceSegment_010_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2916 13 14, g32p_row02_traceSegment_010_2916_0013, g32p_row02_traceSegment_010_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2943 13 14, g32p_row02_traceSegment_010_2943_0013, g32p_row02_traceSegment_010_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2916 27 27, g32p_row02_traceSegment_010_2916_0027, g32p_row02_traceSegment_010_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2970 13 14, g32p_row02_traceSegment_010_2970_0013, g32p_row02_traceSegment_010_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2997 13 14, g32p_row02_traceSegment_010_2997_0013, g32p_row02_traceSegment_010_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2970 27 27, g32p_row02_traceSegment_010_2970_0027, g32p_row02_traceSegment_010_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2916 54 54, g32p_row02_traceSegment_010_2916_0054, g32p_row02_traceSegment_010_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2808 108 108, g32p_row02_traceSegment_010_2808_0108, g32p_row02_traceSegment_010_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2592 216 216, g32p_row02_traceSegment_010_2592_0216, g32p_row02_traceSegment_010_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3024 13 14, g32p_row02_traceSegment_010_3024_0013, g32p_row02_traceSegment_010_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3051 13 14, g32p_row02_traceSegment_010_3051_0013, g32p_row02_traceSegment_010_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3024 27 27, g32p_row02_traceSegment_010_3024_0027, g32p_row02_traceSegment_010_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3078 13 14, g32p_row02_traceSegment_010_3078_0013, g32p_row02_traceSegment_010_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3105 13 14, g32p_row02_traceSegment_010_3105_0013, g32p_row02_traceSegment_010_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3078 27 27, g32p_row02_traceSegment_010_3078_0027, g32p_row02_traceSegment_010_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3024 54 54, g32p_row02_traceSegment_010_3024_0054, g32p_row02_traceSegment_010_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3132 13 14, g32p_row02_traceSegment_010_3132_0013, g32p_row02_traceSegment_010_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3159 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3159 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3159 13 14, g32p_row02_traceSegment_010_3159_0013, g32p_row02_traceSegment_010_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3132 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3132 27 27, g32p_row02_traceSegment_010_3132_0027, g32p_row02_traceSegment_010_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3186 13 14, g32p_row02_traceSegment_010_3186_0013, g32p_row02_traceSegment_010_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3213 13 14, g32p_row02_traceSegment_010_3213_0013, g32p_row02_traceSegment_010_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3186 27 27, g32p_row02_traceSegment_010_3186_0027, g32p_row02_traceSegment_010_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3132 54 54, g32p_row02_traceSegment_010_3132_0054, g32p_row02_traceSegment_010_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 3024 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3024 108 108, g32p_row02_traceSegment_010_3024_0108, g32p_row02_traceSegment_010_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3240 13 14, g32p_row02_traceSegment_010_3240_0013, g32p_row02_traceSegment_010_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3267 13 14, g32p_row02_traceSegment_010_3267_0013, g32p_row02_traceSegment_010_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3240 27 27, g32p_row02_traceSegment_010_3240_0027, g32p_row02_traceSegment_010_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3294 13 14, g32p_row02_traceSegment_010_3294_0013, g32p_row02_traceSegment_010_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3321 13 14, g32p_row02_traceSegment_010_3321_0013, g32p_row02_traceSegment_010_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3294 27 27, g32p_row02_traceSegment_010_3294_0027, g32p_row02_traceSegment_010_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3240 54 54, g32p_row02_traceSegment_010_3240_0054, g32p_row02_traceSegment_010_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3348 13 14, g32p_row02_traceSegment_010_3348_0013, g32p_row02_traceSegment_010_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3375 13 14, g32p_row02_traceSegment_010_3375_0013, g32p_row02_traceSegment_010_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3348 27 27, g32p_row02_traceSegment_010_3348_0027, g32p_row02_traceSegment_010_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3402 13 14, g32p_row02_traceSegment_010_3402_0013, g32p_row02_traceSegment_010_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_010 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_010 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_010_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_010 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3429 13 14, g32p_row02_traceSegment_010_3429_0013, g32p_row02_traceSegment_010_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_010 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3402 27 27, g32p_row02_traceSegment_010_3402_0027, g32p_row02_traceSegment_010_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_010 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3348 54 54, g32p_row02_traceSegment_010_3348_0054, g32p_row02_traceSegment_010_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_010 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3240 108 108, g32p_row02_traceSegment_010_3240_0108, g32p_row02_traceSegment_010_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_010_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_010 3024 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 3024 216 216, g32p_row02_traceSegment_010_3024_0216, g32p_row02_traceSegment_010_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_010_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_010 2592 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 2592 432 432, g32p_row02_traceSegment_010_2592_0432, g32p_row02_traceSegment_010_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_010_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_010 1728 1728 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 1728 864 864, g32p_row02_traceSegment_010_1728_0864, g32p_row02_traceSegment_010_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_010_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_010 0 3456 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_010 0 1728 1728, g32p_row02_traceSegment_010_0000_1728, g32p_row02_traceSegment_010_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 10 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_010_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_011 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 11 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_011_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 0 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 0 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 13 14, g32p_row02_traceSegment_011_0000_0013, g32p_row02_traceSegment_011_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 40 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 27 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 27 13 14, g32p_row02_traceSegment_011_0027_0013, g32p_row02_traceSegment_011_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 0 54 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 27 27, g32p_row02_traceSegment_011_0000_0027, g32p_row02_traceSegment_011_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 54 13 14, g32p_row02_traceSegment_011_0054_0013, g32p_row02_traceSegment_011_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 81 13 14, g32p_row02_traceSegment_011_0081_0013, g32p_row02_traceSegment_011_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 54 27 27, g32p_row02_traceSegment_011_0054_0027, g32p_row02_traceSegment_011_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 0 108 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 54 54, g32p_row02_traceSegment_011_0000_0054, g32p_row02_traceSegment_011_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 108 13 14, g32p_row02_traceSegment_011_0108_0013, g32p_row02_traceSegment_011_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 135 13 14, g32p_row02_traceSegment_011_0135_0013, g32p_row02_traceSegment_011_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 108 27 27, g32p_row02_traceSegment_011_0108_0027, g32p_row02_traceSegment_011_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 162 13 14, g32p_row02_traceSegment_011_0162_0013, g32p_row02_traceSegment_011_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 189 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 189 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 189 13 14, g32p_row02_traceSegment_011_0189_0013, g32p_row02_traceSegment_011_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 162 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 162 27 27, g32p_row02_traceSegment_011_0162_0027, g32p_row02_traceSegment_011_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 108 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 108 54 54, g32p_row02_traceSegment_011_0108_0054, g32p_row02_traceSegment_011_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 0 216 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 108 108, g32p_row02_traceSegment_011_0000_0108, g32p_row02_traceSegment_011_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 229 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 216 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 216 13 14, g32p_row02_traceSegment_011_0216_0013, g32p_row02_traceSegment_011_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 243 13 14, g32p_row02_traceSegment_011_0243_0013, g32p_row02_traceSegment_011_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 216 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 216 27 27, g32p_row02_traceSegment_011_0216_0027, g32p_row02_traceSegment_011_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 283 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 270 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 270 13 14, g32p_row02_traceSegment_011_0270_0013, g32p_row02_traceSegment_011_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 297 13 14, g32p_row02_traceSegment_011_0297_0013, g32p_row02_traceSegment_011_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 270 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 270 27 27, g32p_row02_traceSegment_011_0270_0027, g32p_row02_traceSegment_011_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 216 54 54, g32p_row02_traceSegment_011_0216_0054, g32p_row02_traceSegment_011_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 324 13 14, g32p_row02_traceSegment_011_0324_0013, g32p_row02_traceSegment_011_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 351 13 14, g32p_row02_traceSegment_011_0351_0013, g32p_row02_traceSegment_011_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 324 27 27, g32p_row02_traceSegment_011_0324_0027, g32p_row02_traceSegment_011_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 378 13 14, g32p_row02_traceSegment_011_0378_0013, g32p_row02_traceSegment_011_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 405 13 14, g32p_row02_traceSegment_011_0405_0013, g32p_row02_traceSegment_011_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 378 27 27, g32p_row02_traceSegment_011_0378_0027, g32p_row02_traceSegment_011_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 324 54 54, g32p_row02_traceSegment_011_0324_0054, g32p_row02_traceSegment_011_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 216 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 216 108 108, g32p_row02_traceSegment_011_0216_0108, g32p_row02_traceSegment_011_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 0 432 = [3, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 216 216, g32p_row02_traceSegment_011_0000_0216, g32p_row02_traceSegment_011_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 432 13 14, g32p_row02_traceSegment_011_0432_0013, g32p_row02_traceSegment_011_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 459 13 14, g32p_row02_traceSegment_011_0459_0013, g32p_row02_traceSegment_011_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 432 27 27, g32p_row02_traceSegment_011_0432_0027, g32p_row02_traceSegment_011_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 486 13 14, g32p_row02_traceSegment_011_0486_0013, g32p_row02_traceSegment_011_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 526 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 513 13 14, g32p_row02_traceSegment_011_0513_0013, g32p_row02_traceSegment_011_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 486 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 486 27 27, g32p_row02_traceSegment_011_0486_0027, g32p_row02_traceSegment_011_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 432 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 432 54 54, g32p_row02_traceSegment_011_0432_0054, g32p_row02_traceSegment_011_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 540 13 14, g32p_row02_traceSegment_011_0540_0013, g32p_row02_traceSegment_011_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 567 13 14, g32p_row02_traceSegment_011_0567_0013, g32p_row02_traceSegment_011_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 540 27 27, g32p_row02_traceSegment_011_0540_0027, g32p_row02_traceSegment_011_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 594 13 14, g32p_row02_traceSegment_011_0594_0013, g32p_row02_traceSegment_011_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 621 13 14, g32p_row02_traceSegment_011_0621_0013, g32p_row02_traceSegment_011_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 594 27 27, g32p_row02_traceSegment_011_0594_0027, g32p_row02_traceSegment_011_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 540 54 54, g32p_row02_traceSegment_011_0540_0054, g32p_row02_traceSegment_011_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 432 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 432 108 108, g32p_row02_traceSegment_011_0432_0108, g32p_row02_traceSegment_011_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 648 13 14, g32p_row02_traceSegment_011_0648_0013, g32p_row02_traceSegment_011_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 675 13 14, g32p_row02_traceSegment_011_0675_0013, g32p_row02_traceSegment_011_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 648 27 27, g32p_row02_traceSegment_011_0648_0027, g32p_row02_traceSegment_011_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 715 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 702 13 14, g32p_row02_traceSegment_011_0702_0013, g32p_row02_traceSegment_011_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 729 13 14, g32p_row02_traceSegment_011_0729_0013, g32p_row02_traceSegment_011_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 702 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 702 27 27, g32p_row02_traceSegment_011_0702_0027, g32p_row02_traceSegment_011_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 648 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 648 54 54, g32p_row02_traceSegment_011_0648_0054, g32p_row02_traceSegment_011_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 756 13 14, g32p_row02_traceSegment_011_0756_0013, g32p_row02_traceSegment_011_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 783 13 14, g32p_row02_traceSegment_011_0783_0013, g32p_row02_traceSegment_011_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 756 27 27, g32p_row02_traceSegment_011_0756_0027, g32p_row02_traceSegment_011_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 810 13 14, g32p_row02_traceSegment_011_0810_0013, g32p_row02_traceSegment_011_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 850 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 837 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 837 13 14, g32p_row02_traceSegment_011_0837_0013, g32p_row02_traceSegment_011_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 810 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 810 27 27, g32p_row02_traceSegment_011_0810_0027, g32p_row02_traceSegment_011_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 756 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 756 54 54, g32p_row02_traceSegment_011_0756_0054, g32p_row02_traceSegment_011_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 648 216 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 648 108 108, g32p_row02_traceSegment_011_0648_0108, g32p_row02_traceSegment_011_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 432 432 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 432 216 216, g32p_row02_traceSegment_011_0432_0216, g32p_row02_traceSegment_011_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_011 0 864 = [4, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 432 432, g32p_row02_traceSegment_011_0000_0432, g32p_row02_traceSegment_011_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 864 13 14, g32p_row02_traceSegment_011_0864_0013, g32p_row02_traceSegment_011_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 891 13 14, g32p_row02_traceSegment_011_0891_0013, g32p_row02_traceSegment_011_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 864 27 27, g32p_row02_traceSegment_011_0864_0027, g32p_row02_traceSegment_011_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 918 13 14, g32p_row02_traceSegment_011_0918_0013, g32p_row02_traceSegment_011_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 945 13 14, g32p_row02_traceSegment_011_0945_0013, g32p_row02_traceSegment_011_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 918 27 27, g32p_row02_traceSegment_011_0918_0027, g32p_row02_traceSegment_011_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 864 54 54, g32p_row02_traceSegment_011_0864_0054, g32p_row02_traceSegment_011_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 972 13 14, g32p_row02_traceSegment_011_0972_0013, g32p_row02_traceSegment_011_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 999 13 14, g32p_row02_traceSegment_011_0999_0013, g32p_row02_traceSegment_011_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 972 27 27, g32p_row02_traceSegment_011_0972_0027, g32p_row02_traceSegment_011_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1026 13 14, g32p_row02_traceSegment_011_1026_0013, g32p_row02_traceSegment_011_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1053 13 14, g32p_row02_traceSegment_011_1053_0013, g32p_row02_traceSegment_011_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1026 27 27, g32p_row02_traceSegment_011_1026_0027, g32p_row02_traceSegment_011_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 972 54 54, g32p_row02_traceSegment_011_0972_0054, g32p_row02_traceSegment_011_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 864 108 108, g32p_row02_traceSegment_011_0864_0108, g32p_row02_traceSegment_011_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1080 13 14, g32p_row02_traceSegment_011_1080_0013, g32p_row02_traceSegment_011_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1107 13 14, g32p_row02_traceSegment_011_1107_0013, g32p_row02_traceSegment_011_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1080 27 27, g32p_row02_traceSegment_011_1080_0027, g32p_row02_traceSegment_011_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1134 13 14, g32p_row02_traceSegment_011_1134_0013, g32p_row02_traceSegment_011_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1161 13 14, g32p_row02_traceSegment_011_1161_0013, g32p_row02_traceSegment_011_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1134 27 27, g32p_row02_traceSegment_011_1134_0027, g32p_row02_traceSegment_011_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1080 54 54, g32p_row02_traceSegment_011_1080_0054, g32p_row02_traceSegment_011_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1188 13 14, g32p_row02_traceSegment_011_1188_0013, g32p_row02_traceSegment_011_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1215 13 14, g32p_row02_traceSegment_011_1215_0013, g32p_row02_traceSegment_011_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1188 27 27, g32p_row02_traceSegment_011_1188_0027, g32p_row02_traceSegment_011_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1242 13 14, g32p_row02_traceSegment_011_1242_0013, g32p_row02_traceSegment_011_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1269 13 14, g32p_row02_traceSegment_011_1269_0013, g32p_row02_traceSegment_011_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1242 27 27, g32p_row02_traceSegment_011_1242_0027, g32p_row02_traceSegment_011_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1188 54 54, g32p_row02_traceSegment_011_1188_0054, g32p_row02_traceSegment_011_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1080 108 108, g32p_row02_traceSegment_011_1080_0108, g32p_row02_traceSegment_011_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 864 216 216, g32p_row02_traceSegment_011_0864_0216, g32p_row02_traceSegment_011_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1296 13 14, g32p_row02_traceSegment_011_1296_0013, g32p_row02_traceSegment_011_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1323 13 14, g32p_row02_traceSegment_011_1323_0013, g32p_row02_traceSegment_011_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1296 27 27, g32p_row02_traceSegment_011_1296_0027, g32p_row02_traceSegment_011_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1350 13 14, g32p_row02_traceSegment_011_1350_0013, g32p_row02_traceSegment_011_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1377 13 14, g32p_row02_traceSegment_011_1377_0013, g32p_row02_traceSegment_011_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1350 27 27, g32p_row02_traceSegment_011_1350_0027, g32p_row02_traceSegment_011_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1296 54 54, g32p_row02_traceSegment_011_1296_0054, g32p_row02_traceSegment_011_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1404 13 14, g32p_row02_traceSegment_011_1404_0013, g32p_row02_traceSegment_011_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1431 13 14, g32p_row02_traceSegment_011_1431_0013, g32p_row02_traceSegment_011_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1404 27 27, g32p_row02_traceSegment_011_1404_0027, g32p_row02_traceSegment_011_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1458 13 14, g32p_row02_traceSegment_011_1458_0013, g32p_row02_traceSegment_011_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1485 13 14, g32p_row02_traceSegment_011_1485_0013, g32p_row02_traceSegment_011_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1458 27 27, g32p_row02_traceSegment_011_1458_0027, g32p_row02_traceSegment_011_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1404 54 54, g32p_row02_traceSegment_011_1404_0054, g32p_row02_traceSegment_011_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1296 108 108, g32p_row02_traceSegment_011_1296_0108, g32p_row02_traceSegment_011_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1512 13 14, g32p_row02_traceSegment_011_1512_0013, g32p_row02_traceSegment_011_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1539 13 14, g32p_row02_traceSegment_011_1539_0013, g32p_row02_traceSegment_011_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1512 27 27, g32p_row02_traceSegment_011_1512_0027, g32p_row02_traceSegment_011_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1566 13 14, g32p_row02_traceSegment_011_1566_0013, g32p_row02_traceSegment_011_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1593 13 14, g32p_row02_traceSegment_011_1593_0013, g32p_row02_traceSegment_011_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1566 27 27, g32p_row02_traceSegment_011_1566_0027, g32p_row02_traceSegment_011_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1512 54 54, g32p_row02_traceSegment_011_1512_0054, g32p_row02_traceSegment_011_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1633 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1620 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1620 13 14, g32p_row02_traceSegment_011_1620_0013, g32p_row02_traceSegment_011_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1647 13 14, g32p_row02_traceSegment_011_1647_0013, g32p_row02_traceSegment_011_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1620 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1620 27 27, g32p_row02_traceSegment_011_1620_0027, g32p_row02_traceSegment_011_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1674 13 14, g32p_row02_traceSegment_011_1674_0013, g32p_row02_traceSegment_011_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1701 13 14, g32p_row02_traceSegment_011_1701_0013, g32p_row02_traceSegment_011_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1674 27 27, g32p_row02_traceSegment_011_1674_0027, g32p_row02_traceSegment_011_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1620 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1620 54 54, g32p_row02_traceSegment_011_1620_0054, g32p_row02_traceSegment_011_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 1512 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1512 108 108, g32p_row02_traceSegment_011_1512_0108, g32p_row02_traceSegment_011_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 1296 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1296 216 216, g32p_row02_traceSegment_011_1296_0216, g32p_row02_traceSegment_011_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_011 864 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 864 432 432, g32p_row02_traceSegment_011_0864_0432, g32p_row02_traceSegment_011_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_011 0 1728 = [4, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 864 864, g32p_row02_traceSegment_011_0000_0864, g32p_row02_traceSegment_011_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 13 14, g32p_row02_traceSegment_011_1728_0013, g32p_row02_traceSegment_011_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1755 13 14, g32p_row02_traceSegment_011_1755_0013, g32p_row02_traceSegment_011_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 27 27, g32p_row02_traceSegment_011_1728_0027, g32p_row02_traceSegment_011_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1782 13 14, g32p_row02_traceSegment_011_1782_0013, g32p_row02_traceSegment_011_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1809 13 14, g32p_row02_traceSegment_011_1809_0013, g32p_row02_traceSegment_011_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1782 27 27, g32p_row02_traceSegment_011_1782_0027, g32p_row02_traceSegment_011_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 54 54, g32p_row02_traceSegment_011_1728_0054, g32p_row02_traceSegment_011_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1836 13 14, g32p_row02_traceSegment_011_1836_0013, g32p_row02_traceSegment_011_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1863 13 14, g32p_row02_traceSegment_011_1863_0013, g32p_row02_traceSegment_011_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1836 27 27, g32p_row02_traceSegment_011_1836_0027, g32p_row02_traceSegment_011_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1890 13 14, g32p_row02_traceSegment_011_1890_0013, g32p_row02_traceSegment_011_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1917 13 14, g32p_row02_traceSegment_011_1917_0013, g32p_row02_traceSegment_011_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1890 27 27, g32p_row02_traceSegment_011_1890_0027, g32p_row02_traceSegment_011_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1836 54 54, g32p_row02_traceSegment_011_1836_0054, g32p_row02_traceSegment_011_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 108 108, g32p_row02_traceSegment_011_1728_0108, g32p_row02_traceSegment_011_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1944 13 14, g32p_row02_traceSegment_011_1944_0013, g32p_row02_traceSegment_011_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1971 13 14, g32p_row02_traceSegment_011_1971_0013, g32p_row02_traceSegment_011_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1944 27 27, g32p_row02_traceSegment_011_1944_0027, g32p_row02_traceSegment_011_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1998 13 14, g32p_row02_traceSegment_011_1998_0013, g32p_row02_traceSegment_011_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2025 13 14, g32p_row02_traceSegment_011_2025_0013, g32p_row02_traceSegment_011_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1998 27 27, g32p_row02_traceSegment_011_1998_0027, g32p_row02_traceSegment_011_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1944 54 54, g32p_row02_traceSegment_011_1944_0054, g32p_row02_traceSegment_011_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2052 13 14, g32p_row02_traceSegment_011_2052_0013, g32p_row02_traceSegment_011_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2079 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2092 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2079 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2079 13 14, g32p_row02_traceSegment_011_2079_0013, g32p_row02_traceSegment_011_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2052 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2052 27 27, g32p_row02_traceSegment_011_2052_0027, g32p_row02_traceSegment_011_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2106 13 14, g32p_row02_traceSegment_011_2106_0013, g32p_row02_traceSegment_011_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2146 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2133 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2133 13 14, g32p_row02_traceSegment_011_2133_0013, g32p_row02_traceSegment_011_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2106 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2106 27 27, g32p_row02_traceSegment_011_2106_0027, g32p_row02_traceSegment_011_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2052 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2052 54 54, g32p_row02_traceSegment_011_2052_0054, g32p_row02_traceSegment_011_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 1944 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1944 108 108, g32p_row02_traceSegment_011_1944_0108, g32p_row02_traceSegment_011_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 216 216, g32p_row02_traceSegment_011_1728_0216, g32p_row02_traceSegment_011_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2160 13 14, g32p_row02_traceSegment_011_2160_0013, g32p_row02_traceSegment_011_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2187 13 14, g32p_row02_traceSegment_011_2187_0013, g32p_row02_traceSegment_011_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2160 27 27, g32p_row02_traceSegment_011_2160_0027, g32p_row02_traceSegment_011_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2214 13 14, g32p_row02_traceSegment_011_2214_0013, g32p_row02_traceSegment_011_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2241 13 14, g32p_row02_traceSegment_011_2241_0013, g32p_row02_traceSegment_011_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2214 27 27, g32p_row02_traceSegment_011_2214_0027, g32p_row02_traceSegment_011_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2160 54 54, g32p_row02_traceSegment_011_2160_0054, g32p_row02_traceSegment_011_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2268 13 14, g32p_row02_traceSegment_011_2268_0013, g32p_row02_traceSegment_011_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2295 13 14, g32p_row02_traceSegment_011_2295_0013, g32p_row02_traceSegment_011_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2268 27 27, g32p_row02_traceSegment_011_2268_0027, g32p_row02_traceSegment_011_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2322 13 14, g32p_row02_traceSegment_011_2322_0013, g32p_row02_traceSegment_011_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2349 13 14, g32p_row02_traceSegment_011_2349_0013, g32p_row02_traceSegment_011_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2322 27 27, g32p_row02_traceSegment_011_2322_0027, g32p_row02_traceSegment_011_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2268 54 54, g32p_row02_traceSegment_011_2268_0054, g32p_row02_traceSegment_011_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2160 108 108, g32p_row02_traceSegment_011_2160_0108, g32p_row02_traceSegment_011_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2376 13 14, g32p_row02_traceSegment_011_2376_0013, g32p_row02_traceSegment_011_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2403 13 14, g32p_row02_traceSegment_011_2403_0013, g32p_row02_traceSegment_011_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2376 27 27, g32p_row02_traceSegment_011_2376_0027, g32p_row02_traceSegment_011_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2430 13 14, g32p_row02_traceSegment_011_2430_0013, g32p_row02_traceSegment_011_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2457 13 14, g32p_row02_traceSegment_011_2457_0013, g32p_row02_traceSegment_011_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2430 27 27, g32p_row02_traceSegment_011_2430_0027, g32p_row02_traceSegment_011_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2376 54 54, g32p_row02_traceSegment_011_2376_0054, g32p_row02_traceSegment_011_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2484 13 14, g32p_row02_traceSegment_011_2484_0013, g32p_row02_traceSegment_011_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2511 13 14, g32p_row02_traceSegment_011_2511_0013, g32p_row02_traceSegment_011_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2484 27 27, g32p_row02_traceSegment_011_2484_0027, g32p_row02_traceSegment_011_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2538 13 14, g32p_row02_traceSegment_011_2538_0013, g32p_row02_traceSegment_011_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2578 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2565 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2565 13 14, g32p_row02_traceSegment_011_2565_0013, g32p_row02_traceSegment_011_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2538 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2538 27 27, g32p_row02_traceSegment_011_2538_0027, g32p_row02_traceSegment_011_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2484 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2484 54 54, g32p_row02_traceSegment_011_2484_0054, g32p_row02_traceSegment_011_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 2376 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2376 108 108, g32p_row02_traceSegment_011_2376_0108, g32p_row02_traceSegment_011_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 2160 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2160 216 216, g32p_row02_traceSegment_011_2160_0216, g32p_row02_traceSegment_011_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 864 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 432 432, g32p_row02_traceSegment_011_1728_0432, g32p_row02_traceSegment_011_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2592 13 14, g32p_row02_traceSegment_011_2592_0013, g32p_row02_traceSegment_011_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2619 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2632 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2619 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2619 13 14, g32p_row02_traceSegment_011_2619_0013, g32p_row02_traceSegment_011_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2592 27 27, g32p_row02_traceSegment_011_2592_0027, g32p_row02_traceSegment_011_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2646 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2646 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2646 13 14, g32p_row02_traceSegment_011_2646_0013, g32p_row02_traceSegment_011_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2673 13 14, g32p_row02_traceSegment_011_2673_0013, g32p_row02_traceSegment_011_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2646 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2646 27 27, g32p_row02_traceSegment_011_2646_0027, g32p_row02_traceSegment_011_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2592 54 54, g32p_row02_traceSegment_011_2592_0054, g32p_row02_traceSegment_011_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2700 13 14, g32p_row02_traceSegment_011_2700_0013, g32p_row02_traceSegment_011_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2727 13 14, g32p_row02_traceSegment_011_2727_0013, g32p_row02_traceSegment_011_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2700 27 27, g32p_row02_traceSegment_011_2700_0027, g32p_row02_traceSegment_011_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2754 13 14, g32p_row02_traceSegment_011_2754_0013, g32p_row02_traceSegment_011_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2781 13 14, g32p_row02_traceSegment_011_2781_0013, g32p_row02_traceSegment_011_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2754 27 27, g32p_row02_traceSegment_011_2754_0027, g32p_row02_traceSegment_011_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2700 54 54, g32p_row02_traceSegment_011_2700_0054, g32p_row02_traceSegment_011_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2592 108 108, g32p_row02_traceSegment_011_2592_0108, g32p_row02_traceSegment_011_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2808 13 14, g32p_row02_traceSegment_011_2808_0013, g32p_row02_traceSegment_011_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2835 13 14, g32p_row02_traceSegment_011_2835_0013, g32p_row02_traceSegment_011_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2808 27 27, g32p_row02_traceSegment_011_2808_0027, g32p_row02_traceSegment_011_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2862 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2875 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2862 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2862 13 14, g32p_row02_traceSegment_011_2862_0013, g32p_row02_traceSegment_011_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2889 13 14, g32p_row02_traceSegment_011_2889_0013, g32p_row02_traceSegment_011_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2862 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2862 27 27, g32p_row02_traceSegment_011_2862_0027, g32p_row02_traceSegment_011_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2808 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2808 54 54, g32p_row02_traceSegment_011_2808_0054, g32p_row02_traceSegment_011_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2916 13 14, g32p_row02_traceSegment_011_2916_0013, g32p_row02_traceSegment_011_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2943 13 14, g32p_row02_traceSegment_011_2943_0013, g32p_row02_traceSegment_011_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2916 27 27, g32p_row02_traceSegment_011_2916_0027, g32p_row02_traceSegment_011_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2970 13 14, g32p_row02_traceSegment_011_2970_0013, g32p_row02_traceSegment_011_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2997 13 14, g32p_row02_traceSegment_011_2997_0013, g32p_row02_traceSegment_011_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2970 27 27, g32p_row02_traceSegment_011_2970_0027, g32p_row02_traceSegment_011_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2916 54 54, g32p_row02_traceSegment_011_2916_0054, g32p_row02_traceSegment_011_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 2808 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2808 108 108, g32p_row02_traceSegment_011_2808_0108, g32p_row02_traceSegment_011_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2592 216 216, g32p_row02_traceSegment_011_2592_0216, g32p_row02_traceSegment_011_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3024 13 14, g32p_row02_traceSegment_011_3024_0013, g32p_row02_traceSegment_011_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3051 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3064 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3051 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3051 13 14, g32p_row02_traceSegment_011_3051_0013, g32p_row02_traceSegment_011_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3024 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3024 27 27, g32p_row02_traceSegment_011_3024_0027, g32p_row02_traceSegment_011_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3078 13 14, g32p_row02_traceSegment_011_3078_0013, g32p_row02_traceSegment_011_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3118 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3105 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3105 13 14, g32p_row02_traceSegment_011_3105_0013, g32p_row02_traceSegment_011_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3078 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3078 27 27, g32p_row02_traceSegment_011_3078_0027, g32p_row02_traceSegment_011_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 3024 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3024 54 54, g32p_row02_traceSegment_011_3024_0054, g32p_row02_traceSegment_011_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3132 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3132 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3132 13 14, g32p_row02_traceSegment_011_3132_0013, g32p_row02_traceSegment_011_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3159 13 14, g32p_row02_traceSegment_011_3159_0013, g32p_row02_traceSegment_011_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3132 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3132 27 27, g32p_row02_traceSegment_011_3132_0027, g32p_row02_traceSegment_011_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3186 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3186 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3186 13 14, g32p_row02_traceSegment_011_3186_0013, g32p_row02_traceSegment_011_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3213 13 14, g32p_row02_traceSegment_011_3213_0013, g32p_row02_traceSegment_011_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3186 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3186 27 27, g32p_row02_traceSegment_011_3186_0027, g32p_row02_traceSegment_011_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 3132 108 = [2, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3132 54 54, g32p_row02_traceSegment_011_3132_0054, g32p_row02_traceSegment_011_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 3024 216 = [2, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3024 108 108, g32p_row02_traceSegment_011_3024_0108, g32p_row02_traceSegment_011_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3253 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3240 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3240 13 14, g32p_row02_traceSegment_011_3240_0013, g32p_row02_traceSegment_011_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3267 13 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3280 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3267 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3267 13 14, g32p_row02_traceSegment_011_3267_0013, g32p_row02_traceSegment_011_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3240 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3240 27 27, g32p_row02_traceSegment_011_3240_0027, g32p_row02_traceSegment_011_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3294 13 14, g32p_row02_traceSegment_011_3294_0013, g32p_row02_traceSegment_011_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3321 13 14, g32p_row02_traceSegment_011_3321_0013, g32p_row02_traceSegment_011_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3294 27 27, g32p_row02_traceSegment_011_3294_0027, g32p_row02_traceSegment_011_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 3240 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3240 54 54, g32p_row02_traceSegment_011_3240_0054, g32p_row02_traceSegment_011_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3348 13 14, g32p_row02_traceSegment_011_3348_0013, g32p_row02_traceSegment_011_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3388 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3375 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3375 13 14, g32p_row02_traceSegment_011_3375_0013, g32p_row02_traceSegment_011_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3348 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3348 27 27, g32p_row02_traceSegment_011_3348_0027, g32p_row02_traceSegment_011_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3402 13 14, g32p_row02_traceSegment_011_3402_0013, g32p_row02_traceSegment_011_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_011 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_011 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_011_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_011 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3429 13 14, g32p_row02_traceSegment_011_3429_0013, g32p_row02_traceSegment_011_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_011 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3402 27 27, g32p_row02_traceSegment_011_3402_0027, g32p_row02_traceSegment_011_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_011 3348 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3348 54 54, g32p_row02_traceSegment_011_3348_0054, g32p_row02_traceSegment_011_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_011 3240 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3240 108 108, g32p_row02_traceSegment_011_3240_0108, g32p_row02_traceSegment_011_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_011_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_011 3024 432 = [2, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 3024 216 216, g32p_row02_traceSegment_011_3024_0216, g32p_row02_traceSegment_011_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_011_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_011 2592 864 = [7, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 2592 432 432, g32p_row02_traceSegment_011_2592_0432, g32p_row02_traceSegment_011_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_011_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_011 1728 1728 = [12, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 1728 864 864, g32p_row02_traceSegment_011_1728_0864, g32p_row02_traceSegment_011_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_011_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_011 0 3456 = [16, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_011 0 1728 1728, g32p_row02_traceSegment_011_0000_1728, g32p_row02_traceSegment_011_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 11 = [16, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_011_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_013_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 13 14, g32p_row02_traceSegment_013_0000_0013, g32p_row02_traceSegment_013_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 27 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 27 13 14, g32p_row02_traceSegment_013_0027_0013, g32p_row02_traceSegment_013_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 27 27, g32p_row02_traceSegment_013_0000_0027, g32p_row02_traceSegment_013_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 54 13 14, g32p_row02_traceSegment_013_0054_0013, g32p_row02_traceSegment_013_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 81 13 14, g32p_row02_traceSegment_013_0081_0013, g32p_row02_traceSegment_013_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 54 27 27, g32p_row02_traceSegment_013_0054_0027, g32p_row02_traceSegment_013_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 54 54, g32p_row02_traceSegment_013_0000_0054, g32p_row02_traceSegment_013_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 108 13 14, g32p_row02_traceSegment_013_0108_0013, g32p_row02_traceSegment_013_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 135 13 14, g32p_row02_traceSegment_013_0135_0013, g32p_row02_traceSegment_013_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 108 27 27, g32p_row02_traceSegment_013_0108_0027, g32p_row02_traceSegment_013_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 162 13 14, g32p_row02_traceSegment_013_0162_0013, g32p_row02_traceSegment_013_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 189 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 189 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 189 13 14, g32p_row02_traceSegment_013_0189_0013, g32p_row02_traceSegment_013_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 162 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 162 27 27, g32p_row02_traceSegment_013_0162_0027, g32p_row02_traceSegment_013_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 108 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 108 54 54, g32p_row02_traceSegment_013_0108_0054, g32p_row02_traceSegment_013_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 0 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 108 108, g32p_row02_traceSegment_013_0000_0108, g32p_row02_traceSegment_013_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 216 13 14, g32p_row02_traceSegment_013_0216_0013, g32p_row02_traceSegment_013_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 243 13 14, g32p_row02_traceSegment_013_0243_0013, g32p_row02_traceSegment_013_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 216 27 27, g32p_row02_traceSegment_013_0216_0027, g32p_row02_traceSegment_013_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 270 13 14, g32p_row02_traceSegment_013_0270_0013, g32p_row02_traceSegment_013_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 297 13 14, g32p_row02_traceSegment_013_0297_0013, g32p_row02_traceSegment_013_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 270 27 27, g32p_row02_traceSegment_013_0270_0027, g32p_row02_traceSegment_013_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 216 54 54, g32p_row02_traceSegment_013_0216_0054, g32p_row02_traceSegment_013_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 324 13 14, g32p_row02_traceSegment_013_0324_0013, g32p_row02_traceSegment_013_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 351 13 14, g32p_row02_traceSegment_013_0351_0013, g32p_row02_traceSegment_013_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 324 27 27, g32p_row02_traceSegment_013_0324_0027, g32p_row02_traceSegment_013_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 391 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 378 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 378 13 14, g32p_row02_traceSegment_013_0378_0013, g32p_row02_traceSegment_013_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 405 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 418 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 405 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 405 13 14, g32p_row02_traceSegment_013_0405_0013, g32p_row02_traceSegment_013_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 378 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 378 27 27, g32p_row02_traceSegment_013_0378_0027, g32p_row02_traceSegment_013_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 324 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 324 54 54, g32p_row02_traceSegment_013_0324_0054, g32p_row02_traceSegment_013_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 216 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 216 108 108, g32p_row02_traceSegment_013_0216_0108, g32p_row02_traceSegment_013_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 0 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 216 216, g32p_row02_traceSegment_013_0000_0216, g32p_row02_traceSegment_013_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 432 13 14, g32p_row02_traceSegment_013_0432_0013, g32p_row02_traceSegment_013_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 459 13 14, g32p_row02_traceSegment_013_0459_0013, g32p_row02_traceSegment_013_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 432 27 27, g32p_row02_traceSegment_013_0432_0027, g32p_row02_traceSegment_013_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 486 13 14, g32p_row02_traceSegment_013_0486_0013, g32p_row02_traceSegment_013_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 513 13 14, g32p_row02_traceSegment_013_0513_0013, g32p_row02_traceSegment_013_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 486 27 27, g32p_row02_traceSegment_013_0486_0027, g32p_row02_traceSegment_013_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 432 54 54, g32p_row02_traceSegment_013_0432_0054, g32p_row02_traceSegment_013_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 540 13 14, g32p_row02_traceSegment_013_0540_0013, g32p_row02_traceSegment_013_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 580 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 567 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 567 13 14, g32p_row02_traceSegment_013_0567_0013, g32p_row02_traceSegment_013_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 540 27 27, g32p_row02_traceSegment_013_0540_0027, g32p_row02_traceSegment_013_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 594 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 594 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 594 13 14, g32p_row02_traceSegment_013_0594_0013, g32p_row02_traceSegment_013_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 621 13 14, g32p_row02_traceSegment_013_0621_0013, g32p_row02_traceSegment_013_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 594 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 594 27 27, g32p_row02_traceSegment_013_0594_0027, g32p_row02_traceSegment_013_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 540 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 540 54 54, g32p_row02_traceSegment_013_0540_0054, g32p_row02_traceSegment_013_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 432 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 432 108 108, g32p_row02_traceSegment_013_0432_0108, g32p_row02_traceSegment_013_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 648 13 14, g32p_row02_traceSegment_013_0648_0013, g32p_row02_traceSegment_013_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 675 13 14, g32p_row02_traceSegment_013_0675_0013, g32p_row02_traceSegment_013_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 648 27 27, g32p_row02_traceSegment_013_0648_0027, g32p_row02_traceSegment_013_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 702 13 14, g32p_row02_traceSegment_013_0702_0013, g32p_row02_traceSegment_013_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 729 13 14, g32p_row02_traceSegment_013_0729_0013, g32p_row02_traceSegment_013_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 702 27 27, g32p_row02_traceSegment_013_0702_0027, g32p_row02_traceSegment_013_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 648 54 54, g32p_row02_traceSegment_013_0648_0054, g32p_row02_traceSegment_013_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 756 13 14, g32p_row02_traceSegment_013_0756_0013, g32p_row02_traceSegment_013_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 783 13 14, g32p_row02_traceSegment_013_0783_0013, g32p_row02_traceSegment_013_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 756 27 27, g32p_row02_traceSegment_013_0756_0027, g32p_row02_traceSegment_013_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 810 13 14, g32p_row02_traceSegment_013_0810_0013, g32p_row02_traceSegment_013_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 837 13 14, g32p_row02_traceSegment_013_0837_0013, g32p_row02_traceSegment_013_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 810 27 27, g32p_row02_traceSegment_013_0810_0027, g32p_row02_traceSegment_013_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 756 54 54, g32p_row02_traceSegment_013_0756_0054, g32p_row02_traceSegment_013_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 648 108 108, g32p_row02_traceSegment_013_0648_0108, g32p_row02_traceSegment_013_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 432 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 432 216 216, g32p_row02_traceSegment_013_0432_0216, g32p_row02_traceSegment_013_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_013 0 864 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 432 432, g32p_row02_traceSegment_013_0000_0432, g32p_row02_traceSegment_013_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 864 13 14, g32p_row02_traceSegment_013_0864_0013, g32p_row02_traceSegment_013_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 891 13 14, g32p_row02_traceSegment_013_0891_0013, g32p_row02_traceSegment_013_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 864 27 27, g32p_row02_traceSegment_013_0864_0027, g32p_row02_traceSegment_013_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 918 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 931 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 918 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 918 13 14, g32p_row02_traceSegment_013_0918_0013, g32p_row02_traceSegment_013_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 945 13 14, g32p_row02_traceSegment_013_0945_0013, g32p_row02_traceSegment_013_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 918 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 918 27 27, g32p_row02_traceSegment_013_0918_0027, g32p_row02_traceSegment_013_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 864 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 864 54 54, g32p_row02_traceSegment_013_0864_0054, g32p_row02_traceSegment_013_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 972 13 14, g32p_row02_traceSegment_013_0972_0013, g32p_row02_traceSegment_013_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 999 13 14, g32p_row02_traceSegment_013_0999_0013, g32p_row02_traceSegment_013_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 972 27 27, g32p_row02_traceSegment_013_0972_0027, g32p_row02_traceSegment_013_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1026 13 14, g32p_row02_traceSegment_013_1026_0013, g32p_row02_traceSegment_013_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1053 13 14, g32p_row02_traceSegment_013_1053_0013, g32p_row02_traceSegment_013_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1026 27 27, g32p_row02_traceSegment_013_1026_0027, g32p_row02_traceSegment_013_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 972 54 54, g32p_row02_traceSegment_013_0972_0054, g32p_row02_traceSegment_013_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 864 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 864 108 108, g32p_row02_traceSegment_013_0864_0108, g32p_row02_traceSegment_013_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1080 13 14, g32p_row02_traceSegment_013_1080_0013, g32p_row02_traceSegment_013_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1107 13 14, g32p_row02_traceSegment_013_1107_0013, g32p_row02_traceSegment_013_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1080 27 27, g32p_row02_traceSegment_013_1080_0027, g32p_row02_traceSegment_013_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1134 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1134 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1134 13 14, g32p_row02_traceSegment_013_1134_0013, g32p_row02_traceSegment_013_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1161 13 14, g32p_row02_traceSegment_013_1161_0013, g32p_row02_traceSegment_013_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1134 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1134 27 27, g32p_row02_traceSegment_013_1134_0027, g32p_row02_traceSegment_013_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1080 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1080 54 54, g32p_row02_traceSegment_013_1080_0054, g32p_row02_traceSegment_013_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1188 13 14, g32p_row02_traceSegment_013_1188_0013, g32p_row02_traceSegment_013_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1215 13 14, g32p_row02_traceSegment_013_1215_0013, g32p_row02_traceSegment_013_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1188 27 27, g32p_row02_traceSegment_013_1188_0027, g32p_row02_traceSegment_013_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1242 13 14, g32p_row02_traceSegment_013_1242_0013, g32p_row02_traceSegment_013_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1269 13 14, g32p_row02_traceSegment_013_1269_0013, g32p_row02_traceSegment_013_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1242 27 27, g32p_row02_traceSegment_013_1242_0027, g32p_row02_traceSegment_013_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1188 54 54, g32p_row02_traceSegment_013_1188_0054, g32p_row02_traceSegment_013_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 1080 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1080 108 108, g32p_row02_traceSegment_013_1080_0108, g32p_row02_traceSegment_013_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 864 432 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 864 216 216, g32p_row02_traceSegment_013_0864_0216, g32p_row02_traceSegment_013_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1296 13 14, g32p_row02_traceSegment_013_1296_0013, g32p_row02_traceSegment_013_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1323 13 14, g32p_row02_traceSegment_013_1323_0013, g32p_row02_traceSegment_013_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1296 27 27, g32p_row02_traceSegment_013_1296_0027, g32p_row02_traceSegment_013_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1350 13 14, g32p_row02_traceSegment_013_1350_0013, g32p_row02_traceSegment_013_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1377 13 14, g32p_row02_traceSegment_013_1377_0013, g32p_row02_traceSegment_013_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1350 27 27, g32p_row02_traceSegment_013_1350_0027, g32p_row02_traceSegment_013_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1296 54 54, g32p_row02_traceSegment_013_1296_0054, g32p_row02_traceSegment_013_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1404 13 14, g32p_row02_traceSegment_013_1404_0013, g32p_row02_traceSegment_013_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1431 13 14, g32p_row02_traceSegment_013_1431_0013, g32p_row02_traceSegment_013_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1404 27 27, g32p_row02_traceSegment_013_1404_0027, g32p_row02_traceSegment_013_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1458 13 14, g32p_row02_traceSegment_013_1458_0013, g32p_row02_traceSegment_013_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1485 13 14, g32p_row02_traceSegment_013_1485_0013, g32p_row02_traceSegment_013_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1458 27 27, g32p_row02_traceSegment_013_1458_0027, g32p_row02_traceSegment_013_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1404 54 54, g32p_row02_traceSegment_013_1404_0054, g32p_row02_traceSegment_013_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1296 108 108, g32p_row02_traceSegment_013_1296_0108, g32p_row02_traceSegment_013_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1512 13 14, g32p_row02_traceSegment_013_1512_0013, g32p_row02_traceSegment_013_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1539 13 14, g32p_row02_traceSegment_013_1539_0013, g32p_row02_traceSegment_013_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1512 27 27, g32p_row02_traceSegment_013_1512_0027, g32p_row02_traceSegment_013_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1579 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1566 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1566 13 14, g32p_row02_traceSegment_013_1566_0013, g32p_row02_traceSegment_013_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1593 13 14, g32p_row02_traceSegment_013_1593_0013, g32p_row02_traceSegment_013_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1566 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1566 27 27, g32p_row02_traceSegment_013_1566_0027, g32p_row02_traceSegment_013_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1512 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1512 54 54, g32p_row02_traceSegment_013_1512_0054, g32p_row02_traceSegment_013_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1633 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1620 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1620 13 14, g32p_row02_traceSegment_013_1620_0013, g32p_row02_traceSegment_013_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1647 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1660 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1647 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1647 13 14, g32p_row02_traceSegment_013_1647_0013, g32p_row02_traceSegment_013_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1620 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1620 27 27, g32p_row02_traceSegment_013_1620_0027, g32p_row02_traceSegment_013_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1674 13 14, g32p_row02_traceSegment_013_1674_0013, g32p_row02_traceSegment_013_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1701 13 14, g32p_row02_traceSegment_013_1701_0013, g32p_row02_traceSegment_013_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1674 27 27, g32p_row02_traceSegment_013_1674_0027, g32p_row02_traceSegment_013_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1620 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1620 54 54, g32p_row02_traceSegment_013_1620_0054, g32p_row02_traceSegment_013_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 1512 216 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1512 108 108, g32p_row02_traceSegment_013_1512_0108, g32p_row02_traceSegment_013_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 1296 432 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1296 216 216, g32p_row02_traceSegment_013_1296_0216, g32p_row02_traceSegment_013_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_013 864 864 = [0, 0, 7, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 864 432 432, g32p_row02_traceSegment_013_0864_0432, g32p_row02_traceSegment_013_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_013 0 1728 = [0, 0, 15, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 864 864, g32p_row02_traceSegment_013_0000_0864, g32p_row02_traceSegment_013_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 13 14, g32p_row02_traceSegment_013_1728_0013, g32p_row02_traceSegment_013_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1755 13 14, g32p_row02_traceSegment_013_1755_0013, g32p_row02_traceSegment_013_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 27 27, g32p_row02_traceSegment_013_1728_0027, g32p_row02_traceSegment_013_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1782 13 14, g32p_row02_traceSegment_013_1782_0013, g32p_row02_traceSegment_013_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1809 13 14, g32p_row02_traceSegment_013_1809_0013, g32p_row02_traceSegment_013_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1782 27 27, g32p_row02_traceSegment_013_1782_0027, g32p_row02_traceSegment_013_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 54 54, g32p_row02_traceSegment_013_1728_0054, g32p_row02_traceSegment_013_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1836 13 14, g32p_row02_traceSegment_013_1836_0013, g32p_row02_traceSegment_013_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1863 13 14, g32p_row02_traceSegment_013_1863_0013, g32p_row02_traceSegment_013_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1836 27 27, g32p_row02_traceSegment_013_1836_0027, g32p_row02_traceSegment_013_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1890 13 14, g32p_row02_traceSegment_013_1890_0013, g32p_row02_traceSegment_013_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1930 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1917 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1917 13 14, g32p_row02_traceSegment_013_1917_0013, g32p_row02_traceSegment_013_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1890 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1890 27 27, g32p_row02_traceSegment_013_1890_0027, g32p_row02_traceSegment_013_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1836 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1836 54 54, g32p_row02_traceSegment_013_1836_0054, g32p_row02_traceSegment_013_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 216 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 108 108, g32p_row02_traceSegment_013_1728_0108, g32p_row02_traceSegment_013_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1944 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1944 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1944 13 14, g32p_row02_traceSegment_013_1944_0013, g32p_row02_traceSegment_013_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1971 13 14, g32p_row02_traceSegment_013_1971_0013, g32p_row02_traceSegment_013_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1944 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1944 27 27, g32p_row02_traceSegment_013_1944_0027, g32p_row02_traceSegment_013_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1998 13 14, g32p_row02_traceSegment_013_1998_0013, g32p_row02_traceSegment_013_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2025 13 14, g32p_row02_traceSegment_013_2025_0013, g32p_row02_traceSegment_013_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1998 27 27, g32p_row02_traceSegment_013_1998_0027, g32p_row02_traceSegment_013_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 1944 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1944 54 54, g32p_row02_traceSegment_013_1944_0054, g32p_row02_traceSegment_013_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2052 13 14, g32p_row02_traceSegment_013_2052_0013, g32p_row02_traceSegment_013_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2079 13 14, g32p_row02_traceSegment_013_2079_0013, g32p_row02_traceSegment_013_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2052 27 27, g32p_row02_traceSegment_013_2052_0027, g32p_row02_traceSegment_013_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2106 13 14, g32p_row02_traceSegment_013_2106_0013, g32p_row02_traceSegment_013_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2133 13 14, g32p_row02_traceSegment_013_2133_0013, g32p_row02_traceSegment_013_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2106 27 27, g32p_row02_traceSegment_013_2106_0027, g32p_row02_traceSegment_013_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2052 54 54, g32p_row02_traceSegment_013_2052_0054, g32p_row02_traceSegment_013_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 1944 216 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1944 108 108, g32p_row02_traceSegment_013_1944_0108, g32p_row02_traceSegment_013_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 432 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 216 216, g32p_row02_traceSegment_013_1728_0216, g32p_row02_traceSegment_013_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2160 13 14, g32p_row02_traceSegment_013_2160_0013, g32p_row02_traceSegment_013_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2187 13 14, g32p_row02_traceSegment_013_2187_0013, g32p_row02_traceSegment_013_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2160 27 27, g32p_row02_traceSegment_013_2160_0027, g32p_row02_traceSegment_013_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2214 13 14, g32p_row02_traceSegment_013_2214_0013, g32p_row02_traceSegment_013_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2254 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2241 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2241 13 14, g32p_row02_traceSegment_013_2241_0013, g32p_row02_traceSegment_013_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2214 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2214 27 27, g32p_row02_traceSegment_013_2214_0027, g32p_row02_traceSegment_013_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2160 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2160 54 54, g32p_row02_traceSegment_013_2160_0054, g32p_row02_traceSegment_013_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2268 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2281 14 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2268 27 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2268 13 14, g32p_row02_traceSegment_013_2268_0013, g32p_row02_traceSegment_013_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2295 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2308 14 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2295 27 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2295 13 14, g32p_row02_traceSegment_013_2295_0013, g32p_row02_traceSegment_013_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2268 54 = [0, 0, 5, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2268 27 27, g32p_row02_traceSegment_013_2268_0027, g32p_row02_traceSegment_013_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2335 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2322 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2322 13 14, g32p_row02_traceSegment_013_2322_0013, g32p_row02_traceSegment_013_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2349 13 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2362 14 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2349 27 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2349 13 14, g32p_row02_traceSegment_013_2349_0013, g32p_row02_traceSegment_013_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2322 54 = [0, 0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2322 27 27, g32p_row02_traceSegment_013_2322_0027, g32p_row02_traceSegment_013_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2268 108 = [0, 0, 8, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2268 54 54, g32p_row02_traceSegment_013_2268_0054, g32p_row02_traceSegment_013_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 2160 216 = [0, 0, 8, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2160 108 108, g32p_row02_traceSegment_013_2160_0108, g32p_row02_traceSegment_013_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2376 13 14, g32p_row02_traceSegment_013_2376_0013, g32p_row02_traceSegment_013_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2403 13 14, g32p_row02_traceSegment_013_2403_0013, g32p_row02_traceSegment_013_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2376 27 27, g32p_row02_traceSegment_013_2376_0027, g32p_row02_traceSegment_013_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2430 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2430 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2430 13 14, g32p_row02_traceSegment_013_2430_0013, g32p_row02_traceSegment_013_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2470 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2457 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2457 13 14, g32p_row02_traceSegment_013_2457_0013, g32p_row02_traceSegment_013_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2430 54 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2430 27 27, g32p_row02_traceSegment_013_2430_0027, g32p_row02_traceSegment_013_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2376 108 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2376 54 54, g32p_row02_traceSegment_013_2376_0054, g32p_row02_traceSegment_013_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2484 13 14, g32p_row02_traceSegment_013_2484_0013, g32p_row02_traceSegment_013_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2524 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2511 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2511 13 14, g32p_row02_traceSegment_013_2511_0013, g32p_row02_traceSegment_013_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2484 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2484 27 27, g32p_row02_traceSegment_013_2484_0027, g32p_row02_traceSegment_013_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2538 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2538 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2538 13 14, g32p_row02_traceSegment_013_2538_0013, g32p_row02_traceSegment_013_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2578 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2565 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2565 13 14, g32p_row02_traceSegment_013_2565_0013, g32p_row02_traceSegment_013_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2538 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2538 27 27, g32p_row02_traceSegment_013_2538_0027, g32p_row02_traceSegment_013_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2484 108 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2484 54 54, g32p_row02_traceSegment_013_2484_0054, g32p_row02_traceSegment_013_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 2376 216 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2376 108 108, g32p_row02_traceSegment_013_2376_0108, g32p_row02_traceSegment_013_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 2160 432 = [0, 0, 9, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2160 216 216, g32p_row02_traceSegment_013_2160_0216, g32p_row02_traceSegment_013_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 864 = [0, 0, 9, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 432 432, g32p_row02_traceSegment_013_1728_0432, g32p_row02_traceSegment_013_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2592 13 14, g32p_row02_traceSegment_013_2592_0013, g32p_row02_traceSegment_013_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2619 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2632 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2619 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2619 13 14, g32p_row02_traceSegment_013_2619_0013, g32p_row02_traceSegment_013_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2592 27 27, g32p_row02_traceSegment_013_2592_0027, g32p_row02_traceSegment_013_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2659 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2646 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2646 13 14, g32p_row02_traceSegment_013_2646_0013, g32p_row02_traceSegment_013_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2673 13 14, g32p_row02_traceSegment_013_2673_0013, g32p_row02_traceSegment_013_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2646 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2646 27 27, g32p_row02_traceSegment_013_2646_0027, g32p_row02_traceSegment_013_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2592 54 54, g32p_row02_traceSegment_013_2592_0054, g32p_row02_traceSegment_013_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2700 13 14, g32p_row02_traceSegment_013_2700_0013, g32p_row02_traceSegment_013_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2727 13 14, g32p_row02_traceSegment_013_2727_0013, g32p_row02_traceSegment_013_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2700 27 27, g32p_row02_traceSegment_013_2700_0027, g32p_row02_traceSegment_013_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2754 13 14, g32p_row02_traceSegment_013_2754_0013, g32p_row02_traceSegment_013_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2781 13 14, g32p_row02_traceSegment_013_2781_0013, g32p_row02_traceSegment_013_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2754 27 27, g32p_row02_traceSegment_013_2754_0027, g32p_row02_traceSegment_013_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2700 54 54, g32p_row02_traceSegment_013_2700_0054, g32p_row02_traceSegment_013_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 216 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2592 108 108, g32p_row02_traceSegment_013_2592_0108, g32p_row02_traceSegment_013_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2808 13 14, g32p_row02_traceSegment_013_2808_0013, g32p_row02_traceSegment_013_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2835 13 14, g32p_row02_traceSegment_013_2835_0013, g32p_row02_traceSegment_013_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2808 27 27, g32p_row02_traceSegment_013_2808_0027, g32p_row02_traceSegment_013_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2862 13 14, g32p_row02_traceSegment_013_2862_0013, g32p_row02_traceSegment_013_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2889 13 14, g32p_row02_traceSegment_013_2889_0013, g32p_row02_traceSegment_013_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2862 27 27, g32p_row02_traceSegment_013_2862_0027, g32p_row02_traceSegment_013_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2808 54 54, g32p_row02_traceSegment_013_2808_0054, g32p_row02_traceSegment_013_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2916 13 14, g32p_row02_traceSegment_013_2916_0013, g32p_row02_traceSegment_013_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2943 13 14, g32p_row02_traceSegment_013_2943_0013, g32p_row02_traceSegment_013_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2916 27 27, g32p_row02_traceSegment_013_2916_0027, g32p_row02_traceSegment_013_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2970 13 14, g32p_row02_traceSegment_013_2970_0013, g32p_row02_traceSegment_013_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2997 13 14, g32p_row02_traceSegment_013_2997_0013, g32p_row02_traceSegment_013_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2970 27 27, g32p_row02_traceSegment_013_2970_0027, g32p_row02_traceSegment_013_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2916 54 54, g32p_row02_traceSegment_013_2916_0054, g32p_row02_traceSegment_013_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2808 108 108, g32p_row02_traceSegment_013_2808_0108, g32p_row02_traceSegment_013_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 432 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2592 216 216, g32p_row02_traceSegment_013_2592_0216, g32p_row02_traceSegment_013_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3024 13 14, g32p_row02_traceSegment_013_3024_0013, g32p_row02_traceSegment_013_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3051 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3064 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3051 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3051 13 14, g32p_row02_traceSegment_013_3051_0013, g32p_row02_traceSegment_013_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3024 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3024 27 27, g32p_row02_traceSegment_013_3024_0027, g32p_row02_traceSegment_013_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3078 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3091 14 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3078 27 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3078 13 14, g32p_row02_traceSegment_013_3078_0013, g32p_row02_traceSegment_013_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3105 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3118 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3105 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3105 13 14, g32p_row02_traceSegment_013_3105_0013, g32p_row02_traceSegment_013_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3078 54 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3078 27 27, g32p_row02_traceSegment_013_3078_0027, g32p_row02_traceSegment_013_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 3024 108 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3024 54 54, g32p_row02_traceSegment_013_3024_0054, g32p_row02_traceSegment_013_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3132 13 14, g32p_row02_traceSegment_013_3132_0013, g32p_row02_traceSegment_013_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3159 13 14, g32p_row02_traceSegment_013_3159_0013, g32p_row02_traceSegment_013_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3132 27 27, g32p_row02_traceSegment_013_3132_0027, g32p_row02_traceSegment_013_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3186 13 14, g32p_row02_traceSegment_013_3186_0013, g32p_row02_traceSegment_013_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3213 13 14, g32p_row02_traceSegment_013_3213_0013, g32p_row02_traceSegment_013_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3186 27 27, g32p_row02_traceSegment_013_3186_0027, g32p_row02_traceSegment_013_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3132 54 54, g32p_row02_traceSegment_013_3132_0054, g32p_row02_traceSegment_013_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 3024 216 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3024 108 108, g32p_row02_traceSegment_013_3024_0108, g32p_row02_traceSegment_013_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3240 13 14, g32p_row02_traceSegment_013_3240_0013, g32p_row02_traceSegment_013_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3267 13 14, g32p_row02_traceSegment_013_3267_0013, g32p_row02_traceSegment_013_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3240 27 27, g32p_row02_traceSegment_013_3240_0027, g32p_row02_traceSegment_013_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3294 13 14, g32p_row02_traceSegment_013_3294_0013, g32p_row02_traceSegment_013_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3321 13 14, g32p_row02_traceSegment_013_3321_0013, g32p_row02_traceSegment_013_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3294 27 27, g32p_row02_traceSegment_013_3294_0027, g32p_row02_traceSegment_013_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3240 54 54, g32p_row02_traceSegment_013_3240_0054, g32p_row02_traceSegment_013_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3348 13 14, g32p_row02_traceSegment_013_3348_0013, g32p_row02_traceSegment_013_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3375 13 14, g32p_row02_traceSegment_013_3375_0013, g32p_row02_traceSegment_013_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3348 27 27, g32p_row02_traceSegment_013_3348_0027, g32p_row02_traceSegment_013_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3402 13 14, g32p_row02_traceSegment_013_3402_0013, g32p_row02_traceSegment_013_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_013 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_013 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_013_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_013 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3429 13 14, g32p_row02_traceSegment_013_3429_0013, g32p_row02_traceSegment_013_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_013 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3402 27 27, g32p_row02_traceSegment_013_3402_0027, g32p_row02_traceSegment_013_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_013 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3348 54 54, g32p_row02_traceSegment_013_3348_0054, g32p_row02_traceSegment_013_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_013 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3240 108 108, g32p_row02_traceSegment_013_3240_0108, g32p_row02_traceSegment_013_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_013_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_013 3024 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 3024 216 216, g32p_row02_traceSegment_013_3024_0216, g32p_row02_traceSegment_013_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_013_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_013 2592 864 = [0, 0, 12, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 2592 432 432, g32p_row02_traceSegment_013_2592_0432, g32p_row02_traceSegment_013_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_013_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_013 1728 1728 = [0, 0, 21, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 1728 864 864, g32p_row02_traceSegment_013_1728_0864, g32p_row02_traceSegment_013_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_013_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_013 0 3456 = [0, 0, 36, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_013 0 1728 1728, g32p_row02_traceSegment_013_0000_1728, g32p_row02_traceSegment_013_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 13 = [0, 0, 36, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_013_0000_3456

end HodgeLean.Foundations.Program

end
end
